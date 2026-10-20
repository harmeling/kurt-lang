import io
import json
import os
import subprocess
import sys
import tempfile
import threading
import time
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

sys.path.insert(0, str(PROJECT_ROOT / 'scripts'))
import grade_exercise   # noqa: E402
sys.path.remove(str(PROJECT_ROOT / 'scripts'))   # (only needed for the import above, not left on sys.path for the rest of the suite)

# the budget of the search for one line (`RunConfig(time_limit=..., step_limit=...)`, `kurt --budget`,
# the editors, the grader) and the cancellation of a check (`RunConfig(cancel=...)`; todo 10,
# 2026-10-16): a line whose budget is used up fails with a `ResourceError` -- apart from a
# `ProofError`, it is neither proved nor refuted -- and a budget that isn't hit changes nothing


def false_case(n: int, scene: bool = False) -> str:
    # a false goal `G` after a disjunction of `n` alternatives, each but the last with its
    # implication, among as many unrelated disjunctions (as scripts/bench_case.py writes them): the
    # search for `G` takes 1.2 s for n = 6, more than 8 s for n = 8 (2026-10-16) -- with `load propositional`
    # only, so no theory has to be checked first. `scene`: the facts labelled, as a theory to load
    alts = [f'A{i}' for i in range(n)]
    noise = [(f'B{j}', f'C{j}', f'H{j}') for j in range(n)]
    label = (lambda name: f' "{name}"') if scene else (lambda name: '')
    lines = ['load propositional', 'prop ' + ', '.join(alts + ['G'] + [s for t in noise for s in t]),
             'use ' + ' or '.join(alts) + label('alternatives')]
    for b, c, h in noise:
        lines += [f'use {b} or {c}{label(b)}', f'use {b} implies {h}{label(b + h)}', f'use {c} implies {h}{label(c + h)}']
    lines += [f'use {a} implies G{label(a + "G")}' for a in alts[:-1]]
    return '\n'.join(lines) + '\n' + ('' if scene else 'G\n')


SLOW = false_case(8)                   # more than 8 s of search, then a `ProofError`
SLOW_LINE = SLOW.count('\n')           # the line of `G`
FALSE = false_case(6)                  # about 1.2 s, a `ProofError`
PROOF = 'load propositional\nprop A, B\nuse A implies B\nuse A\nB\n'


CACHE: dict = {}       # the theories checked so far, shared by the sessions here (as the language server shares them):
                       # propositional.kurt is checked once -- a small budget must not hit its lines on a busy machine
BUDGET = 0.3           # seconds, for a check whose theories are in the cache ...
COLD_BUDGET = 3.0      # ... and for one in a new process or server, which checks propositional.kurt first (0.2 s on a quiet machine), under
                       # the budget too: a line of it took over 1 s on a busy node (2026-10-17, with Lean runs beside it)
GRADER_BUDGET = 3.0    # ... and for the grader, which checks the exercise and the solution, each loading propositional.kurt cold, the same;
                       # the slow line takes over 8 s


def session(**options) -> kurt.Session:
    s = kurt.Session(kurt.RunConfig(**options))
    s._state._checked_exports = CACHE
    return s


def timed(check):
    start = time.monotonic()
    result = check()
    return result, time.monotonic() - start


def lsp_messages(writer: io.BytesIO) -> list[dict]:
    # the JSON-RPC messages a language server wrote
    data, messages = writer.getvalue(), []
    while data:
        header, _, data = data.partition(b'\r\n\r\n')
        length = int(header.split(b':')[1])
        messages.append(json.loads(data[:length]))
        data = data[length:]
    return messages


class TestBudgets(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        session().check_text('load propositional\nload logic\n')         # (into the cache)

    def test_a_time_budget_stops_the_search(self):
        result, seconds = timed(lambda: session(time_limit=BUDGET).check_text(SLOW))
        self.assertFalse(result.ok)
        self.assertEqual((result.error_kind, result.error_line), ('ResourceError', SLOW_LINE))
        self.assertTrue(result.exhausted)
        self.assertFalse(result.cancelled)
        self.assertIn(f'ResourceError: the search for this line stopped after {BUDGET} s, its budget', result.error)
        self.assertIn('neither proved nor refuted', result.error)
        self.assertNotIn('can not derive', result.error)                 # (no rejection)
        self.assertLess(seconds, 2.0, seconds)                           # (the line takes more than 8 s; checked every few ms)
        self.assertEqual(result.errors[0]['kind'], 'ResourceError')
        self.assertEqual(json.loads(result.to_json())['exhausted'], True)
        # without a budget: refuted (the smaller case, in about a second)
        without = session().check_text(FALSE)
        self.assertEqual(without.error_kind, 'ProofError')
        self.assertFalse(without.exhausted or without.cancelled)

    def test_a_step_budget_is_the_same_on_every_machine(self):
        # a step: a goal against one fact, or a premise against the facts (`budget_step`)
        result = session(step_limit=100).check_text(SLOW)
        self.assertEqual(result.error_kind, 'ResourceError')
        self.assertIn('stopped after 100 steps, its budget', result.error)
        self.assertTrue(result.exhausted)
        self.assertEqual(session(step_limit=100).check_text(SLOW).output, result.output)
        self.assertEqual(session(step_limit=10 ** 7).check_text(FALSE).error_kind, 'ProofError')   # (enough steps: refuted, as without)

    def test_a_budget_that_is_not_hit_changes_nothing(self):
        generous = kurt.RunConfig(time_limit=1000, step_limit=10 ** 9)
        for text in (PROOF, 'load logic\nconst a\nuse ∀ $x ($x = $x)\na = a\n', FALSE):
            with self.subTest(text=text[:30]):
                plain, budgeted = kurt.Session().check_text(text), kurt.Session(generous).check_text(text)
                self.assertEqual((budgeted.ok, budgeted.output, budgeted.error), (plain.ok, plain.output, plain.error))
                self.assertFalse(budgeted.exhausted)
        path = str(PROJECT_ROOT / 'proofs' / 'natural-deduction' / 'contraposition.kurt')
        self.assertEqual(kurt.Session(generous).check_file(path).output, kurt.Session().check_file(path).output)

    def test_the_closings_at_the_end_of_a_file_have_their_own_budget(self):
        # the end of the file closes a proof (a derived line after its last one, `7a`): no line is
        # being checked then, so its search counted from the start of the run -- an immediate
        # `ResourceError` in the editors (found by tests/test_lsp.py, 2026-10-16) -- any budget catches
        # that (its clock started at 0); 0.5 s was too little for propositional.kurt's own closings, checked
        # cold on a busy node (2026-10-17)
        text = 'load propositional\nprop A, B, C\nuse A\nuse A implies B\nshow B or C\nproof\n    B\n'
        result = session(time_limit=COLD_BUDGET, all_errors=True).check_text(text)
        self.assertTrue(result.ok, result.error)
        self.assertIn('; 7a by or-intro(7)', result.output)
        with tempfile.TemporaryDirectory() as tmp:               # the same at the end of a loaded file
            with open(os.path.join(tmp, 'closing.kurt'), 'w', encoding='utf-8') as f:
                f.write(text.replace('show B or C', 'show B or C "it"'))
            result = session(time_limit=COLD_BUDGET, paths=(tmp,)).check_text('load closing\nB or C\n')
            self.assertTrue(result.ok, result.error)

    def test_the_kernel_is_not_involved(self):
        # the budget is checked in the search only (`impl_elim`, `match_all_theory`), never while
        # the kernel verifies a step -- and a used-up budget is no kernel verdict
        original = kurt.budget_step
        def guarded():
            frame = sys._getframe(1)
            while frame is not None:
                self.assertNotIn(frame.f_code.co_name, ('kernel_verify', 'kernel_verify_block', 'record_certificate'))
                frame = frame.f_back
            original()
        kurt.budget_step = guarded
        try:
            result = session(time_limit=BUDGET).check_text(SLOW)
        finally:
            kurt.budget_step = original
        self.assertEqual(result.error_kind, 'ResourceError')
        self.assertNotIn('KernelError', result.error)

    def test_expect_does_not_catch_it(self):
        # a budget is no verdict, so `expect "ProofError"` isn't confirmed by it -- and a proof file
        # can't name it (`expect "ResourceError"`), as it can't name a `KernelError`
        def expecting(text: str) -> str:
            lines = text.rstrip('\n').split('\n')
            return '\n'.join(lines[:-1] + ['expect "ProofError"', '    ' + lines[-1]]) + '\n'
        self.assertTrue(session().check_text(expecting(FALSE)).ok)      # without a budget: the expected rejection
        result = session(time_limit=BUDGET).check_text(expecting(SLOW))
        self.assertEqual(result.error_kind, 'ResourceError')
        self.assertIn('expect "ProofError" expected a `ProofError`, got a different error instead', result.error)
        self.assertTrue(result.exhausted)
        named = kurt.check_text('expect "ResourceError"\n    prop A\n')
        self.assertEqual(named.error_kind, 'EvalError')
        self.assertIn('unknown error kind `ResourceError`', named.error)

    def test_all_errors_goes_on_after_it(self):
        # the line is admitted (as a `todo` would), the lines after it are checked; the budget
        # starts again for each line
        # (`Z)`: an error that is found at once -- any false claim among these facts is slow)
        result = session(time_limit=BUDGET, all_errors=True).check_text(SLOW + 'prop Z\nZ)\n')
        self.assertEqual([(e['kind'], e['line']) for e in result.errors], [('ResourceError', SLOW_LINE), ('ParseError', SLOW_LINE + 2)])
        self.assertTrue(result.exhausted)
        self.assertFalse(result.cancelled)
        self.assertIn('Proof not checked: 2 errors.', result.output)
        self.assertIn('ResourceError:', result.output)                   # (printed where it happened)

    def test_a_cancelled_check_stops(self):
        # `cancel` is asked at every step and every line; the check stops at the line it is at,
        # also with all errors (the lines after it are not checked)
        asked = [0]
        def after_a_while() -> bool:                  # (the lines before the slow one ask fewer than 100 times: no search)
            asked[0] += 1
            return asked[0] > 500
        result = session(cancel=after_a_while, all_errors=True).check_text(SLOW + 'prop Z\nZ)\n')
        self.assertEqual((result.error_kind, result.error_line), ('ResourceError', SLOW_LINE))
        self.assertTrue(result.cancelled)
        self.assertFalse(result.exhausted)
        self.assertIn('the check was cancelled at this line', result.error)
        self.assertEqual(len(result.errors), 1, result.errors)           # (not the `ParseError` of the line after it)
        # from another thread, e.g. a `threading.Event` (where the check is when it is set depends on the machine)
        event = threading.Event()
        timer = threading.Timer(0.3, event.set)
        timer.start()
        try:
            result, seconds = timed(lambda: session(cancel=event.is_set).check_text(SLOW))
        finally:
            timer.cancel()
        self.assertEqual((result.error_kind, result.cancelled), ('ResourceError', True))
        self.assertLessEqual(result.error_line, SLOW_LINE)
        self.assertLess(seconds, 2.0)
        # at a line boundary too, where there is no search
        result = session(cancel=lambda: True).check_text('prop A, B\nprop C\n')
        self.assertEqual((result.error_kind, result.error_line, result.cancelled), ('ResourceError', 1, True))
        # a check that isn't cancelled: as without
        self.assertEqual(session(cancel=lambda: False).check_text(PROOF).output, kurt.check_text(PROOF).output)

    def test_the_command_line_has_a_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'slow.kurt')
            with open(path, 'w', encoding='utf-8') as f:
                f.write(SLOW)
            done = subprocess.run([sys.executable, str(PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py'), '--no-kurtc', '--json', '--budget', str(COLD_BUDGET), path],
                                  capture_output=True, text=True, cwd=tmp)
            self.assertEqual(done.returncode, 1)
            result = json.loads(done.stdout)
            self.assertEqual((result['error_kind'], result['error_line'], result['exhausted'], result['cancelled']),
                             ('ResourceError', SLOW_LINE, True, False))
            self.assertEqual([e['error_kind'] for e in result['events'] if e['kind'] == 'error'], ['ResourceError'])
            done = subprocess.run([sys.executable, str(PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py'), '--no-kurtc', '--budget', str(COLD_BUDGET), path],
                                  capture_output=True, text=True, cwd=tmp)
            self.assertEqual(done.returncode, 1)
            self.assertIn(f'ResourceError: the search for this line stopped after {COLD_BUDGET:g} s', done.stderr)

    def test_the_language_server_names_the_budget(self):
        # the editors: a diagnostic at the line, saying it is the budget (the option `budget`,
        # 30 s by default)
        writer = io.BytesIO()
        server = kurt.LanguageServer(io.BytesIO(), writer)
        self.assertEqual(server.budget, 30.0)
        server.handle({'jsonrpc': '2.0', 'id': 1, 'method': 'initialize', 'params': {'initializationOptions': {'budget': COLD_BUDGET}}})
        uri = 'file:///tmp/budget.kurt'
        server.texts[uri], server.versions[uri] = SLOW, 1
        server.check(uri)
        published = [m for m in lsp_messages(writer) if m.get('method') == 'textDocument/publishDiagnostics']
        errors = [d for d in published[-1]['params']['diagnostics'] if d['severity'] == 1]
        self.assertEqual(len(errors), 1)
        self.assertEqual(errors[0]['range']['start']['line'], SLOW_LINE - 1)
        self.assertTrue(errors[0]['message'].startswith(f'ResourceError: the search for this line stopped after {COLD_BUDGET:g} s, its budget'), errors[0]['message'])
        self.assertTrue(server.results[uri].exhausted)
        # `budget: 0`: none
        server.handle({'jsonrpc': '2.0', 'id': 2, 'method': 'initialize', 'params': {'initializationOptions': {'budget': 0}}})
        self.assertIsNone(server.session_for(uri).config.time_limit)

    def test_the_language_server_stops_a_stale_check(self):
        # a check of a text that is edited meanwhile stops (before: the check of the new text waited
        # for it -- here more than 8 s)
        server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
        server.budget = 0
        uri = 'file:///tmp/stale.kurt'
        server.texts[uri], server.versions[uri] = SLOW, 1
        thread = threading.Thread(target=server.check, args=(uri, 1))
        start = time.monotonic()
        thread.start()
        time.sleep(0.5)
        with server.state_lock:
            server.texts[uri], server.versions[uri] = PROOF, 2                # edited
        thread.join(timeout=60)
        self.assertFalse(thread.is_alive())
        self.assertLess(time.monotonic() - start, 3.0)
        self.assertNotIn(uri, server.results)                            # (the stale result is discarded)
        self.assertEqual(lsp_messages(server.writer), [])                # (no diagnostics for the old text)
        server.check(uri, 2)
        self.assertTrue(server.results[uri].ok)

    def test_the_grader_has_a_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.mkdir(os.path.join(tmp, 'theory'))
            exercise, solution = os.path.join(tmp, 'ex.kurt'), os.path.join(tmp, 'sol.kurt')
            with open(os.path.join(tmp, 'theory', 'scene.kurt'), 'w', encoding='utf-8') as f:
                f.write(false_case(8, scene=True))                       # (the facts of the scene, trusted)
            with open(exercise, 'w', encoding='utf-8') as f:
                f.write('load scene\nshow G\nproof\n    todo\nqed\n')
            with open(solution, 'w', encoding='utf-8') as f:
                f.write('load scene\nshow G\nproof\n    G\nqed\n')
            complete, report = grade_exercise.grade(grade_exercise.Path(exercise), grade_exercise.Path(solution), budget=GRADER_BUDGET)
            self.assertFalse(complete)
            self.assertIn(f'not decided: line 4 took more than {GRADER_BUDGET:g} s of search (the budget', report)
            self.assertIn('ResourceError', report)
            self.assertNotIn('can not derive', report)
            done = subprocess.run([sys.executable, str(PROJECT_ROOT / 'scripts' / 'grade_exercise.py'), '--budget', str(GRADER_BUDGET), exercise, solution],
                                  capture_output=True, text=True, cwd=tmp)
            self.assertEqual(done.returncode, 1, done.stderr)
            self.assertIn('not decided', done.stdout)


if __name__ == '__main__':
    unittest.main()
