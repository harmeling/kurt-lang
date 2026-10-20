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

PROOF = '''load propositional, numbers
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
        thm = self.result.foundation('thm')
        self.assertEqual((thm['class'], thm['status']), ('theorem', 'established'))
        self.assertEqual(rests_on(thm), [('use', 'mine.kurt', 'ax-a'), ('use', 'mine.kurt', 'ax-ab'), ('use', 'propositional.kurt', 'and-intro')])
        self.assertEqual(kurt.foundation_summary(thm), 'established, relative to 3 axioms')
        five = self.result.foundation('five')
        self.assertEqual(five['status'], 'established')
        self.assertEqual([(p['kind'], p['label']) for p in five['rests_on']], [('def', 'c-def'), ('calc', 'five')])
        self.assertIn('`+` add', five['rests_on'][1]['text'])                 # the calculator's bindings
        self.assertEqual(kurt.foundation_summary(five), 'established, relative to 1 definition and the calculator')

    def test_the_class_of_a_fact_stays_what_it_is(self):
        # an axiom is an axiom, a definition a definition -- whatever its label says; an unused axiom is listed too
        self.assertEqual([(e['label'], e['class']) for e in self.result.foundations],
                         [('ax-a', 'axiom'), ('ax-ab', 'axiom'), ('unused', 'axiom'), ('c-def', 'definition'), ('thm', 'theorem'),
                          ('id', 'theorem'), ('gap', 'theorem'), ('five', 'theorem'), ('bare', 'theorem')])
        self.assertEqual(self.result.foundation('ax-a')['rests_on'], [])
        self.assertEqual(self.result.foundation('c-def')['text'], 'c = 2 + 3')      # without its label
        self.assertIsNone(self.result.foundation('nothing'))

    def test_a_discharged_assumption_is_no_postulate(self):
        # `C ⇒ C` by impl-intro: the `assume C` is a hypothesis of the block, not an axiom
        entry = self.result.foundation('id')
        self.assertEqual(entry['rests_on'], [])
        self.assertEqual(kurt.foundation_summary(entry), 'established, rests on nothing but the rules of Kurt')

    def test_a_todo_in_the_proof(self):
        gap = self.result.foundation('gap')
        self.assertEqual(gap['status'], 'accepted')
        self.assertEqual(rests_on(gap), [('use', 'mine.kurt', 'ax-a'), ('use', 'mine.kurt', 'ax-ab'), ('todo', 'mine.kurt', 'C')])
        self.assertEqual(kurt.foundation_summary(gap), 'accepted relative to 1 todo (and 2 axioms)')
        bare = self.result.foundation('bare')                                  # `qed` admitted by a bare `todo`: that line
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
                self.assertEqual(rests_on(result.foundation('main')),
                                 [('use', 'main.kurt', 'ax-qr'), ('use', 't.kurt', 'ax-p'), ('use', 't.kurt', 'ax-pq')])
                self.assertEqual(result.foundation('main')['rests_on'][1]['file'], os.path.join(d, 't.kurt'))

    def test_blocks_and_a_pick(self):
        # a `let` block, a `pick` (its witness's fact is discharged, the existential it comes from counts)
        text = ('load logic\nuse ∀x (P(x) ⇒ Q(x)) "pq"\nuse ∃x P(x) "some-p"\nshow ∃x Q(x) "thm"\nproof\n'
                '    pick c with P(c)\n        Q(c)\n        ∃x Q(x)\nqed\n'
                'show ∀x (P(x) ⇒ Q(x) ∧ P(x)) "all"\nproof\n    let x\n        assume P(x)\n            Q(x)\n            Q(x) ∧ P(x)\nqed\n')
        result = kurt.Session().check_text(text, 'blocks.kurt', foundation=True)
        self.assertTrue(result.ok, result.error)
        # (`Q(c)` from "pq" and `P(c)` in one step: the `∀` is instantiated by the search, no "forall-elim" is cited)
        self.assertEqual(rests_on(result.foundation('thm')),
                         [('use', 'blocks.kurt', 'pq'), ('use', 'blocks.kurt', 'some-p'), ('use', 'logic.kurt', 'exists-intro')])
        self.assertEqual(rests_on(result.foundation('all')), [('use', 'blocks.kurt', 'pq'), ('use', 'propositional.kurt', 'and-intro')])

    def test_a_proof_file(self):
        result = kurt.Session().check_file(str(PROJECT_ROOT / 'proofs' / 'natural-deduction' / 'contraposition.kurt'), foundation=True)
        self.assertTrue(result.complete, result.error)
        entry = result.foundation('contraposition')
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


class TestFoundationCommandLine(unittest.TestCase):
    def run_kurt(self, *args: str) -> subprocess.CompletedProcess:
        env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
        return subprocess.run([sys.executable, '-m', 'kurt.kurt', '--no-kurtc', *args], capture_output=True, text=True, env=env, cwd=PROJECT_ROOT)

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


if __name__ == '__main__':
    unittest.main()
