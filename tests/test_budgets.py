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


def false_case(n: int, scene: bool = False, decoy: bool = False) -> str:
    # a false goal `G` after a disjunction of `n` alternatives, each but the last with its
    # implication, among as many unrelated disjunctions (as scripts/bench_case.py writes them) -- with
    # `load propositional` only, so no theory has to be checked first. `scene`: the facts labelled, as
    # a theory to load. The search tried every split of the alternatives among the groups of
    # "or-elim"/"-3"/"-4": 1.2 s for n = 6, more than 8 s for n = 8 (2026-10-16); since 2026-10-23 only if
    # the premises `Ai ⇒ G` can cover the alternatives (`hopeless_split`): 0.2 s for n = 16. `decoy`: a
    # rule `(A0 ∨ (D ∧ %X)) ⇒ G` too, whose premise with a variable might fit any group -- then every
    # split was tried again (16 s for n = 8, 2026-10-23); since 2026-10-24 its part `D ∧ %X` is one of
    # the alternatives it may unify with, none here (0.06 s)
    alts = [f'A{i}' for i in range(n)]
    noise = [(f'B{j}', f'C{j}', f'H{j}') for j in range(n)]
    label = (lambda name: f' "{name}"') if scene else (lambda name: '')
    lines = ['load propositional', 'prop ' + ', '.join(alts + ['G'] + [s for t in noise for s in t]),
             'use ' + ' or '.join(alts) + label('alternatives')]
    for b, c, h in noise:
        lines += [f'use {b} or {c}{label(b)}', f'use {b} implies {h}{label(b + h)}', f'use {c} implies {h}{label(c + h)}']
    lines += [f'use {a} implies G{label(a + "G")}' for a in alts[:-1]]
    if decoy:
        lines += ['prop D', f'use ({alts[0]} or (D and %X)) implies G{label("decoy")}']
    return '\n'.join(lines) + '\n' + ('' if scene else 'G\n')


def shared_case(n: int, scene: bool = False) -> str:
    # a false goal `G` after a disjunction of `n` alternatives, two of them `D ∧ P` and `E ∧ Q`, whose
    # groups of four the rules `(A0 ∨ A4 ∨ ...) ⇒ G`, ... could cover, if the last one's premise
    # `A3 ∨ ... ∨ (D ∧ %X) ∨ (E ∧ %X)` could take both: `hopeless_split` took each part of it for an
    # alternative it may unify with, alone, and couldn't tell that the two need different values of `%X`
    # -- so "or-elim-4" tried every split (1.7 s for n = 7, 7.4 s for n = 8, 2026-10-24); since
    # 2026-10-25 the parts are unified together (0.05 s for n = 32; todo 50)
    alts = [f'A{i}' for i in range(n - 2)]
    label = (lambda name: f' "{name}"') if scene else (lambda name: '')
    lines = ['load propositional', 'prop ' + ', '.join(alts + ['G', 'D', 'E', 'P', 'Q']),
             'use ' + ' or '.join(alts + ['(D and P)', '(E and Q)']) + label('alternatives')]
    lines += [f'use ({" or ".join(alts[j::4])}) implies G{label(f"group{j}")}' for j in range(3)]
    lines += ['use (' + ' or '.join(alts[3::4] + ['(D and %X)', '(E and %X)']) + ') implies G' + label('decoy')]
    return '\n'.join(lines) + '\n' + ('' if scene else 'G\n')


def twice_case(n: int, scene: bool = False) -> str:
    # a false goal `G` after a disjunction of `n` alternatives, the last one twice (`A0 ∨ ... ∨ A7 ∨ A7`),
    # each but the last with its implication: `hopeless_split` takes the alternatives for a set, so
    # with one twice it can't tell, and every split is tried (1.3 s for n = 7, 5.8 s for n = 8, 25 s
    # for n = 9; what is left of todo 50, 2026-10-25)
    alts = [f'A{i}' for i in range(n - 1)]
    label = (lambda name: f' "{name}"') if scene else (lambda name: '')
    lines = ['load propositional', 'prop ' + ', '.join(alts + ['G']),
             'use ' + ' or '.join(alts + [alts[-1]]) + label('alternatives')]
    lines += [f'use {a} implies G{label(a + "G")}' for a in alts[:-1]]
    return '\n'.join(lines) + '\n' + ('' if scene else 'G\n')


SLOW = twice_case(9)                   # more than 8 s of search, then a `ProofError`
SLOW_LINE = SLOW.count('\n')           # the line of `G`
FALSE = twice_case(6)                  # about 0.4 s, a `ProofError`
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
        self.assertIn(f'ResourceError: the search for this line stopped after {BUDGET} s, its budget', result.error or '')
        self.assertIn('neither proved nor refuted', result.error or '')
        self.assertNotIn('can not derive', result.error or '')                 # (no rejection)
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
        self.assertIn('stopped after 100 steps, its budget', result.error or '')
        self.assertTrue(result.exhausted)
        self.assertEqual(session(step_limit=100).check_text(SLOW).output, result.output)
        self.assertEqual(session(step_limit=10 ** 7).check_text(FALSE).error_kind, 'ProofError')   # (enough steps: refuted, as without)

    def test_a_false_goal_after_a_disjunction_is_refuted_without_trying_every_split(self):
        # todo 50: the alternative without an implication can be in no group (`hopeless_split`), so no
        # split of the 12 alternatives is tried -- before, 20000 steps weren't enough
        result = session(step_limit=2000).check_text(false_case(12))
        self.assertEqual(result.error_kind, 'ProofError', result.error)
        self.assertIn('can not derive `G`', result.error or '')
        # and with a rule whose premise has a variable, `(A0 ∨ (D ∧ %X)) ⇒ G`: its part `D ∧ %X` fits
        # no alternative, so it gives no group (2026-10-24) -- before, every split was tried again
        result = session(step_limit=2000).check_text(false_case(12, decoy=True))
        self.assertEqual(result.error_kind, 'ProofError', result.error)
        self.assertIn('can not derive `G`', result.error or '')
        # and with a premise whose parts need two values of one variable, `... ∨ (D ∧ %X) ∨ (E ∧ %X)`
        # against `D ∧ P` and `E ∧ Q`: the parts are unified together (2026-10-25) -- before, every split
        result = session(step_limit=2000).check_text(shared_case(12))
        self.assertEqual(result.error_kind, 'ProofError', result.error)
        self.assertIn('can not derive `G`', result.error or '')
        # and with `load logic`: "forall-elim" `(∀ $$x %A) ⇒ sub $$x $a %A` fits each premise `%A ⇒ G`,
        # its premise a binder, which fits no alternative (2026-10-25) -- before, it might be any group
        result = session(step_limit=2000).check_text(false_case(12).replace('load propositional', 'load logic'))
        self.assertEqual(result.error_kind, 'ProofError', result.error)
        self.assertIn('can not derive `G`', result.error or '')
        # ... and the diagnosis after it: `(A0 ∨ ∀ y %X)` four times against the 12 alternatives is no
        # match by the count of its parts (`cannot_unify`, a binder matches one argument, 2026-10-25)
        text = false_case(12).replace('load propositional', 'load logic').replace('\nG\n', '\nuse (A0 or (forall y %X)) implies G\nG\n')
        result, seconds = timed(lambda: session().check_text(text))
        self.assertEqual(result.error_kind, 'ProofError', result.error)
        self.assertLess(seconds, 2.0)

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
        self.assertNotIn('KernelError', result.error or '')

    def test_expect_does_not_catch_it(self):
        # a budget is no verdict, so `expect "ProofError"` isn't confirmed by it -- and a proof file
        # can't name it (`expect "ResourceError"`), as it can't name a `KernelError`
        def expecting(text: str) -> str:
            lines = text.rstrip('\n').split('\n')
            return '\n'.join(lines[:-1] + ['expect "ProofError"', '    ' + lines[-1]]) + '\n'
        self.assertTrue(session().check_text(expecting(FALSE)).ok)      # without a budget: the expected rejection
        result = session(time_limit=BUDGET).check_text(expecting(SLOW))
        self.assertEqual(result.error_kind, 'ResourceError')
        self.assertIn('expect "ProofError" expected a `ProofError`, got a different error instead', result.error or '')
        self.assertTrue(result.exhausted)
        named = kurt.check_text('expect "ResourceError"\n    prop A\n')
        self.assertEqual(named.error_kind, 'EvalError')
        self.assertIn('unknown error kind `ResourceError`', named.error or '')

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
        self.assertIn('the check was cancelled at this line', result.error or '')
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
        assert result.error_line is not None
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

    def test_an_embedder_stops_the_language_servers_check(self):
        # todo 51: the playground runs the server in a worker, one check at a time, which can't read a
        # message while it checks -- its Cancel button sets a flag in a SharedArrayBuffer, which
        # `LanguageServer.cancel` reads (here: a flag set by a timer). The check stops at its next step,
        # publishes nothing, and the same server checks the next text (before: the worker was killed, and
        # Pyodide and the theories loaded again)
        server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
        server.budget = 0
        flag = threading.Event()
        server.cancel = flag.is_set
        uri = 'file:///tmp/cancel.kurt'
        server.texts[uri], server.versions[uri] = SLOW, 1
        timer = threading.Timer(0.5, flag.set)
        start = time.monotonic()
        timer.start()
        try:
            server.check(uri, 1)            # (in this thread, as in the worker)
        finally:
            timer.cancel()
        self.assertLess(time.monotonic() - start, 3.0)
        self.assertNotIn(uri, server.results)
        self.assertEqual(lsp_messages(server.writer), [])
        flag.clear()                        # (the playground clears the flag before the next check)
        server.texts[uri], server.versions[uri] = PROOF, 2
        server.check(uri, 2)
        self.assertTrue(server.results[uri].ok)

    def test_the_grader_has_a_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.mkdir(os.path.join(tmp, 'theory'))
            exercise, solution = os.path.join(tmp, 'ex.kurt'), os.path.join(tmp, 'sol.kurt')
            with open(os.path.join(tmp, 'theory', 'scene.kurt'), 'w', encoding='utf-8') as f:
                f.write(twice_case(9, scene=True))                     # (the facts of the scene, trusted)
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
