import io
import json
import os
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt

from tests.utils import PROJECT_ROOT

# what a fact rests on (todo 6, 2026-10-16): the `use` axioms, `def`s, `todo`s and calculator steps
# behind its proof, found by walking the certificates of its steps (`foundation`); for each top-level
# fact of a file with its class (`file_foundations`; `kurt --foundation FILE`, `--json`,
# `CheckResult.foundations`)

PROOF = '''load propositional, number
prop A, B, C
use A "ax-a"
use A implies B "ax-ab"
use C "unused"
def c = 2 + 3 "c-def"
show A and B "thm"
proof
    B
    A and B
qed
show C implies C "id"
proof
    assume C
        C
qed
show B and C "gap"
proof
    todo C
    B and C
qed
calc on
c = 5 "five"
show B "bare"
proof
    todo
qed
'''

THEORY = '''load propositional
prop P, Q
use P "ax-p"
use P implies Q "ax-pq"
Q "thm-q"
'''


def entry_of(result: kurt.CheckResult, label: str) -> dict:
    entry = result.foundation(label)
    assert entry is not None, f'no entry for {label!r}'
    return entry


def rests_on(entry: dict) -> list[tuple[str, str, str]]:
    return [(p['kind'], os.path.basename(p['file']), p['label'] or p['text'] or p['line']) for p in entry['rests_on']]


def theory_line(theory: str, label: str) -> int:
    # the line `label` is declared at in a theory shipped with Kurt -- found here rather than
    # hardcoded, so a line that moves (a comment added above it, say) doesn't silently make a test
    # assert a stale number
    path = PROJECT_ROOT / 'src' / 'kurt' / 'theories' / theory
    with open(path, encoding='utf-8') as f:
        for i, line in enumerate(f, start=1):
            if f'"{label}"' in line:
                return i
    raise AssertionError(f'label {label!r} not found in {theory}')


class TestFoundation(unittest.TestCase):
    def setUp(self):
        self.result = kurt.Session().check_text(PROOF, 'mine.kurt', foundation=True)
        self.assertTrue(self.result.ok, self.result.error)

    def test_a_theorem_resting_on_axioms_and_a_definition(self):
        thm = entry_of(self.result, 'thm')
        self.assertEqual((thm['class'], thm['status']), ('theorem', 'established'))
        self.assertEqual(rests_on(thm), [('use', 'mine.kurt', 'ax-a'), ('use', 'mine.kurt', 'ax-ab'), ('use', 'propositional.kurt', 'and-intro')])
        self.assertEqual(kurt.foundation_summary(thm), 'established, relative to 3 axioms')
        five = entry_of(self.result, 'five')
        self.assertEqual(five['status'], 'established')
        self.assertEqual([(p['kind'], p['label']) for p in five['rests_on']], [('def', 'c-def'), ('calc', 'five')])
        self.assertIn('`+` add', five['rests_on'][1]['text'])                 # the calculator's bindings
        self.assertEqual(kurt.foundation_summary(five), 'established, relative to 1 definition and the calculator')

    def test_the_class_of_a_fact_stays_what_it_is(self):
        # an axiom is an axiom, a definition a definition -- whatever its label says; an unused axiom is listed too
        self.assertEqual([(e['label'], e['class']) for e in self.result.foundations],
                         [('ax-a', 'axiom'), ('ax-ab', 'axiom'), ('unused', 'axiom'), ('c-def', 'definition'), ('thm', 'theorem'),
                          ('id', 'theorem'), ('gap', 'theorem'), ('five', 'theorem'), ('bare', 'theorem')])
        self.assertEqual(entry_of(self.result, 'ax-a')['rests_on'], [])
        self.assertEqual(entry_of(self.result, 'c-def')['text'], 'c = 2 + 3')      # without its label
        self.assertIsNone(self.result.foundation('nothing'))

    def test_a_discharged_assumption_is_no_postulate(self):
        # `C ⇒ C` by impl-intro: the `assume C` is a hypothesis of the block, not an axiom
        entry = entry_of(self.result, 'id')
        self.assertEqual(entry['rests_on'], [])
        self.assertEqual(kurt.foundation_summary(entry), 'established, rests on nothing but the rules of Kurt')

    def test_a_todo_in_the_proof(self):
        gap = entry_of(self.result, 'gap')
        self.assertEqual(gap['status'], 'accepted')
        self.assertEqual(rests_on(gap), [('use', 'mine.kurt', 'ax-a'), ('use', 'mine.kurt', 'ax-ab'), ('todo', 'mine.kurt', 'C')])
        self.assertEqual(kurt.foundation_summary(gap), 'accepted relative to 1 todo (and 2 axioms)')
        bare = entry_of(self.result, 'bare')                                  # `qed` admitted by a bare `todo`: that line
        self.assertEqual([(p['kind'], p['line'], p['text']) for p in bare['rests_on']], [('todo', '26', '')])
        self.assertEqual(kurt.foundation_summary(bare), 'accepted relative to 1 todo')

    def test_a_loaded_theory(self):
        # a theorem of a loaded file keeps its foundation: the axioms of that file, by file -- also
        # when the loaded file comes from the session's cache (the second check)
        with tempfile.TemporaryDirectory() as d:
            d = os.path.realpath(d)   # kurt resolves a loaded file's path; macOS's /tmp is a symlink
            with open(os.path.join(d, 't.kurt'), 'w', encoding='utf-8') as f:
                f.write(THEORY)
            session = kurt.Session(kurt.RunConfig(paths=(d,)))
            for _ in range(2):
                result = session.check_text('load t\nprop R\nuse Q implies R "ax-qr"\nR "main"\n', 'main.kurt', foundation=True)
                self.assertTrue(result.ok, result.error)
                self.assertEqual(rests_on(entry_of(result, 'main')),
                                 [('use', 'main.kurt', 'ax-qr'), ('use', 't.kurt', 'ax-p'), ('use', 't.kurt', 'ax-pq')])
                self.assertEqual(entry_of(result, 'main')['rests_on'][1]['file'], os.path.join(d, 't.kurt'))

    def test_blocks_and_a_pick(self):
        # a `let` block, a `pick` (its witness's fact is discharged, the existential it comes from counts)
        text = ('load logic\nuse ∀x (P(x) ⇒ Q(x)) "pq"\nuse ∃x P(x) "some-p"\nshow ∃x Q(x) "thm"\nproof\n'
                '    pick c with P(c)\n        Q(c)\n        ∃x Q(x)\nqed\n'
                'show ∀x (P(x) ⇒ Q(x) ∧ P(x)) "all"\nproof\n    let x\n        assume P(x)\n            Q(x)\n            Q(x) ∧ P(x)\nqed\n')
        result = kurt.Session().check_text(text, 'blocks.kurt', foundation=True)
        self.assertTrue(result.ok, result.error)
        # (`Q(c)` from "pq" and `P(c)` in one step: the `∀` is instantiated by the search, no "forall-elim" is cited)
        self.assertEqual(rests_on(entry_of(result, 'thm')),
                         [('use', 'blocks.kurt', 'pq'), ('use', 'blocks.kurt', 'some-p'), ('use', 'logic.kurt', 'exists-intro')])
        self.assertEqual(rests_on(entry_of(result, 'all')), [('use', 'blocks.kurt', 'pq'), ('use', 'propositional.kurt', 'and-intro')])

    def test_a_proof_file(self):
        result = kurt.Session().check_file(str(PROJECT_ROOT / 'proofs' / 'natural-deduction' / 'contraposition.kurt'), foundation=True)
        self.assertTrue(result.complete, result.error)
        entry = entry_of(result, 'contraposition')
        self.assertEqual(entry['status'], 'established')
        self.assertIn(('use', 'propositional.kurt', 'iff-subst'), rests_on(entry))
        self.assertTrue(any(p['file'].startswith('<chain transitivity') for p in entry['rests_on']))   # the rules of its `chain`
        report = kurt.foundation_report('contraposition.kurt', result.foundations)
        self.assertIn('the rules of `chain iff invimplies`: "chain-trans-0-0" (line 1)', report)
        self.assertIn('each postulate, and the facts above that rest on it:', report)

    def test_without_foundation_nothing_is_computed(self):
        self.assertEqual(kurt.check_text(PROOF).foundations, [])

    def test_the_report(self):
        report = kurt.foundation_report('mine.kurt', self.result.foundations)
        self.assertIn(f'"thm" (line 7, theorem): established, relative to 3 axioms\n    mine.kurt: "ax-a" (line 3), "ax-ab" (line 4)\n    propositional.kurt: "and-intro" (line {theory_line("propositional.kurt", "and-intro")})', report)
        self.assertIn('"gap" (line 17, theorem): accepted relative to 1 todo (and 2 axioms)\n    mine.kurt: "ax-a" (line 3), "ax-ab" (line 4), todo `C` (line 19)', report)
        self.assertIn('"bare" (line 24, theorem): accepted relative to 1 todo\n    mine.kurt: todo at line 26', report)
        self.assertIn('"c-def" (line 6, definition): a definition (`def`): conservative, rests on nothing', report)
        self.assertIn('mine.kurt: "ax-a" (line 3): "thm", "gap"', report)         # the reverse: who rests on the axiom


def run_kurt(*args: str) -> subprocess.CompletedProcess:
    env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
    return subprocess.run([sys.executable, '-m', 'kurt.kurt', '--no-kurtc', *args], capture_output=True, text=True, env=env, cwd=PROJECT_ROOT)


class TestFoundationCommandLine(unittest.TestCase):
    def run_kurt(self, *args: str) -> subprocess.CompletedProcess:
        return run_kurt(*args)

    def test_foundation_option(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, 'mine.kurt')
            with open(path, 'w', encoding='utf-8') as f:
                f.write(PROOF)
            run = self.run_kurt('--foundation', path)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertTrue(run.stdout.startswith('mine.kurt: what each fact at its top level rests on\n'), run.stdout)
            self.assertIn('"five" (line 23, theorem): established, relative to 1 definition and the calculator', run.stdout)
            self.assertIn('line 23 computed by the calculator (`+` add', run.stdout)
            with open(path, 'w', encoding='utf-8') as f:
                f.write('load propositional\nprop A\nA\n')
            run = self.run_kurt('--foundation', path)
            self.assertEqual(run.returncode, 1)
            self.assertIn('ProofError', run.stderr)

    def test_json(self):
        with tempfile.TemporaryDirectory() as d:
            d = os.path.realpath(d)   # kurt resolves a loaded file's path; macOS's /tmp is a symlink
            path = os.path.join(d, 'mine.kurt')
            with open(path, 'w', encoding='utf-8') as f:
                f.write(PROOF)
            run = self.run_kurt('--json', path)
            self.assertEqual(run.returncode, 0, run.stderr)
            data = json.loads(run.stdout)
            gap = next(e for e in data['foundations'] if e['label'] == 'gap')
            self.assertEqual(gap['status'], 'accepted')
            self.assertEqual([p['kind'] for p in gap['rests_on']], ['use', 'use', 'todo'])
            self.assertEqual(gap['rests_on'][2], {'kind': 'todo', 'file': path, 'line': '19', 'label': '', 'text': 'C'})


# the leftovers of todo 64 (2026-10-24): unlabelled axioms and definitions as entries, the files that
# bound a `calc` step's symbols, `--foundation LABEL FILE`, the editors' hover, and one walk of the
# certificates for `rests_on_admission` and `foundation` (`certificate_uses`)

UNLABELLED = '''load propositional
prop A, B, C
use A
use A implies B
def D iff B
B and A
show B "d"
proof
    A
    B
qed
'''


class TestFoundationLeftovers(unittest.TestCase):
    def test_unlabelled_axioms_and_definitions_are_entries(self):
        # an unlabelled `use` is as much an axiom of the file as a labelled one -- before, only the
        # theorems resting on it showed it (and only in the reverse index)
        result = kurt.Session().check_text(UNLABELLED, 'u.kurt', foundation=True)
        self.assertTrue(result.ok, result.error)
        self.assertEqual([(e['line'], e['label'], e['class']) for e in result.foundations],
                         [('3', '', 'axiom'), ('4', '', 'axiom'), ('5', '', 'definition'), ('6', '', 'theorem'), ('7', 'd', 'theorem')])
        self.assertEqual(entry_of(result, '4')['text'], 'A implies B')
        report = kurt.foundation_report('u.kurt', result.foundations)
        self.assertIn('\nline 3 `A` (axiom): an axiom (`use`): assumed, not proved\n', report)
        self.assertIn('\nline 5 `D iff B` (definition): a definition (`def`)', report)
        self.assertIn('\nline 6 `B and A` (theorem): established, relative to 2 axioms\n', report)
        self.assertIn('    u.kurt: use `A` (line 3): line 6, "d"', report)          # (the reverse index: a fact without a label by its line)

    def test_a_calc_step_names_the_file_that_bound_its_symbols(self):
        result = kurt.Session().check_text(PROOF, 'mine.kurt', foundation=True)
        calc = entry_of(result, 'five')['rests_on'][1]
        self.assertEqual(calc['kind'], 'calc')
        self.assertEqual([os.path.basename(f) for f in calc['bound_in']], ['number.kurt'])
        self.assertIn('(`+` add, `=` eq of number.kurt)', calc['text'])
        # a symbol bound in the file itself: that file
        own = kurt.Session().check_text('load number\ninfix == 40 40\nbuiltin == eq\ncalc on\n1 + 1 == 2 "two"\n', 'own.kurt', foundation=True)
        self.assertTrue(own.ok, own.error)
        calc = entry_of(own, 'two')['rests_on'][0]
        self.assertEqual(calc['bound_in'], ['own.kurt'])
        self.assertIn('(`==` eq of own.kurt)', calc['text'])

    def test_the_report_of_one_fact(self):
        result = kurt.Session().check_text(PROOF, 'mine.kurt', foundation=True)
        thm = kurt.foundation_report_of(entry_of(result, 'thm'), result.foundations)
        self.assertEqual(thm, f'"thm" (line 7, theorem): established, relative to 3 axioms\n    mine.kurt: "ax-a" (line 3), "ax-ab" (line 4)\n'
                              f'    propositional.kurt: "and-intro" (line {theory_line("propositional.kurt", "and-intro")})')
        axiom = kurt.foundation_report_of(entry_of(result, 'ax-a'), result.foundations)
        self.assertEqual(axiom, '"ax-a" (line 3, axiom): an axiom (`use`): assumed, not proved\n    resting on it: "thm", "gap"')
        unused = kurt.foundation_report_of(entry_of(result, 'unused'), result.foundations)
        self.assertTrue(unused.endswith('resting on it: no fact at the top level of the file'), unused)

    def test_one_fact_on_the_command_line(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, 'mine.kurt')
            with open(path, 'w', encoding='utf-8') as f:
                f.write(PROOF)
            for args in (('--foundation', 'thm', path), (path, '--foundation', 'thm'), ('--foundation', '7', path)):
                run = run_kurt(*args)
                self.assertEqual(run.returncode, 0, run.stderr)
                self.assertTrue(run.stdout.startswith('"thm" (line 7, theorem): established, relative to 3 axioms\n'), run.stdout)
                self.assertNotIn('"gap"', run.stdout)                         # (only that fact)
            run = run_kurt('--foundation', 'nothing', path)
            self.assertEqual(run.returncode, 1)
            self.assertIn('no fact "nothing" at the top level of mine.kurt (its labels: "ax-a"', run.stderr)

    def test_the_hover_says_what_a_theorem_rests_on(self):
        with tempfile.TemporaryDirectory() as tmp:
            uri = 'file://' + os.path.join(tmp, 'mine.kurt')
            server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
            server.texts[uri], server.versions[uri] = PROOF, 1
            server.check(uri)
            def hover(line: int) -> str:
                found = server.hover({'textDocument': {'uri': uri}, 'position': {'line': line - 1, 'character': 0}})
                return found['contents']['value'] if found else ''
            self.assertIn('**rests on:** 2 axioms of mine.kurt, 1 axiom of propositional.kurt, no todo', hover(7))
            self.assertIn('**rests on:** nothing but the rules of Kurt, no todo', hover(12))
            self.assertIn('**rests on:** 2 axioms of mine.kurt, 1 todo', hover(17))
            self.assertIn('**rests on:** 1 def, the calculator, no todo', hover(23))
            self.assertNotIn('rests on', hover(3))                            # (an axiom: it is one)
            self.assertNotIn('rests on', hover(9))                            # (a line inside a proof)

    def test_the_hover_names_the_rules_of_a_chain(self):
        entry = {'class': 'theorem', 'rests_on': [{'kind': 'use', 'file': "<chain transitivity for ['=', '<']>", 'line': '1', 'label': 'chain-trans-0-0', 'text': ''},
                                                  {'kind': 'admitted', 'file': 'f.kurt', 'line': '3', 'label': '', 'text': ''}]}
        self.assertEqual(kurt.foundation_in_short(entry), 'rests on: 1 rule of `chain = <`, no todo, 1 line admitted after an error')

    def test_one_walk_for_admissions_and_foundations(self):
        # `rests_on_admission` (at the check, one step deep) and `foundation` (to the leaves, after
        # it) follow the same edges, `certificate_uses`: a theorem whose foundation has a `todo` or
        # an admitted line is itself admitted -- in each file with a `todo` among the tests
        files = [PROJECT_ROOT / 'proofs' / 'debug' / 'todo.kurt', PROJECT_ROOT / 'proofs' / 'debug' / 'todo-admits-only-the-next-step.kurt']
        for path in files:
            session = kurt.Session()
            result = session.check_file(str(path), foundation=True)
            self.assertTrue(result.ok, result.error)
            with session._active():
                theory = next(facts for f, facts in kurt.run_state.file_theories.items() if os.path.basename(f) == path.name)
                checked = 0
                for f in theory:
                    if f.keyword != '' or not isinstance(f.reason, kurt.Reason):
                        continue
                    if kurt.foundation_status(kurt.foundation(f, result._kb)) == 'accepted':
                        self.assertTrue(f.admitted, (path.name, f.line))
                    for cert in f.reason.certificates:
                        checked += 1
                        self.assertEqual(kurt.rests_on_admission([cert]),
                                         cert.kind == 'todo' or any(g.admitted for g in kurt.certificate_uses(cert)))
                self.assertGreater(checked, 0, path.name)
        # and the ones of PROOF: the theorems resting on a `todo` are the admitted ones
        result = kurt.Session().check_text(PROOF, 'mine.kurt', foundation=True)
        self.assertEqual([e['label'] for e in result.foundations if e['status'] == 'accepted'], ['gap', 'bare'])
        self.assertEqual([c for c in ('thm', 'id', 'gap', 'five', 'bare') if not result.proves(entry_of(result, c)['text'], c)], ['gap', 'bare'])


if __name__ == '__main__':
    unittest.main()
