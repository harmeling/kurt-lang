import os
import sys
import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

sys.path.insert(0, str(PROJECT_ROOT / 'scripts'))
import grade_exercise   # noqa: E402
sys.path.remove(str(PROJECT_ROOT / 'scripts'))   # (only needed for the import above, not left on sys.path for the rest of the suite)

# The named-goal grading API (todo 7, 2026-10-16): `CheckResult.proves(statement, label)` says
# whether the file proves the statement at its top level -- derived here by steps that rest on
# no admission -- and `proof_of` how it states it ('proved', 'admitted', 'assumed', 'loaded',
# None); `CheckResult.loaded` names the files it loaded. The grader (scripts/grade_exercise.py)
# builds on them: each `show` of the exercise must be proved, nothing else may be loaded.

PROVED = 'load propositional\nprop A, B\nshow A ∧ B ⇒ A "t"\nproof\n    assume A ∧ B\n        A\nqed\n'


class TestProves(unittest.TestCase):
    def test_a_proved_statement(self):
        result = kurt.check_text(PROVED)
        self.assertTrue(result.complete)
        self.assertTrue(result.proves('A ∧ B ⇒ A'))
        self.assertEqual(result.proof_of('A ∧ B ⇒ A'), 'proved')
        self.assertTrue(result.proves('(A and B) implies A'))         # another notation: the same statement
        self.assertTrue(result.proves('B ∧ A ⇒ A'))                    # `∧` is `sym`
        self.assertTrue(result.proves('show A ∧ B ⇒ A "t"'))           # as the line of an exercise
        self.assertTrue(result.proves('A ∧ B ⇒ A', 't'))
        self.assertFalse(result.proves('A ∧ B ⇒ A', 'wrong'))          # with the wrong label
        self.assertFalse(result.proves('A ∧ B ⇒ A "wrong"'))
        self.assertFalse(result.proves('A ∧ B ⇒ B'))                   # another statement
        self.assertFalse(result.proves('A'))

    def test_the_statement_is_read_in_the_file_s_context(self):
        result = kurt.check_text(PROVED)
        self.assertIsNone(result.proof_of('A says B'))                 # `says` isn't declared: not stated, not an error
        self.assertIsNone(result.proof_of('A ∧ ⇒'))                    # unreadable: not stated
        with self.assertRaises(ValueError):
            result.proof_of('use A')                                   # not a statement

    def test_a_used_statement_is_assumed_not_proved(self):
        result = kurt.check_text('load propositional\nprop A\nuse A "a"\ndef B ⇔ A\n')
        self.assertFalse(result.proves('A'))
        self.assertEqual(result.proof_of('A'), 'assumed')
        self.assertEqual(result.proof_of('B ⇔ A'), 'assumed')
        restated = kurt.check_text('load propositional\nprop A, B\nuse A "a"\nuse B\nA\n')
        self.assertTrue(restated.proves('A'))                          # derived (from the file's own axiom: not under `strict`)
        last = kurt.check_text('load propositional\nprop A\nuse A "a"\nA\n')
        self.assertEqual(last.proof_of('A'), 'assumed')                # restating the last line adds nothing

    def test_a_todo_admits(self):
        text = ('load propositional\nprop A, B\ntodo B "b"\n'
                'show A ⇒ B\nproof\n    todo\nqed\n'                   # the joker closes the proof
                'show A ⇒ A ∨ B\nproof\n    assume A\n        todo\n        B\n        A ∨ B\nqed\n'   # a `todo` deep inside (and not even needed)
                'show B ∨ A\nproof\n    B ∨ A\nqed\n'                  # a proof from an admitted fact
                'show A ⇒ A\nproof\n    assume A\n        A\nqed\n')   # a real proof, between them
        result = kurt.check_text(text)
        self.assertTrue(result.ok)
        self.assertFalse(result.complete)
        for statement in ('B', 'A ⇒ B', 'A ⇒ A ∨ B', 'B ∨ A'):
            with self.subTest(statement=statement):
                self.assertFalse(result.proves(statement))
                self.assertEqual(result.proof_of(statement), 'admitted')
        self.assertTrue(result.proves('A ⇒ A'))

    def test_an_admission_is_followed_through_the_blocks(self):
        # a `todo` outside the proof, used by it through `pick`, `let`, `case` and a chain
        cases = {
            'pick': 'load logic\nvar x\nprop P 0, Q\narity P 1\nuse ∃ x P(x) "e"\ntodo ∀ x (P(x) ⇒ Q)\n'
                    'show Q\nproof\n    pick x with P(x)\n        Q\nqed\n',
            'pick from': 'load logic\nvar x\nprop P 0, Q\narity P 1\ntodo ∃ x P(x) "e"\nuse ∀ x (P(x) ⇒ Q)\n'
                         'show Q\nproof\n    pick x with P(x)\n        Q\nqed\n',
            'let': 'load logic\nvar x\nprop P 0, Q 0\narity P 1, Q 1\ntodo ∀ x P(x)\nuse ∀ x (P(x) ⇒ Q(x))\n'
                   'show ∀ x Q(x)\nproof\n    let x\n        P(x)\n        Q(x)\nqed\n',
            'case': 'load propositional\nprop A, B\ntodo A ∨ B\nuse A ⇒ B\nshow B\nproof\n    case A ∨ B\n        case A\n            B\n'
                    '        case B\n            B\n        B\nqed\n',
            'chain': 'load natural\nconst a\ntodo a < 2 "t"\ncalc on\nshow a < 3\nproof\n    a < 2 < 3\nqed\n',
        }
        for name, text in cases.items():
            with self.subTest(block=name):
                admitted = kurt.check_text(text)
                self.assertTrue(admitted.ok, admitted.error)
                statement = text.split('show ')[1].split('\n')[0]
                self.assertEqual(admitted.proof_of(statement), 'admitted')
                proved = kurt.check_text(text.replace('todo ', 'use ', 1))
                self.assertTrue(proved.complete, proved.error)
                self.assertTrue(proved.proves(statement))

    def test_a_withdrawn_claim_is_not_stated(self):
        result = kurt.check_text('load propositional\nprop A\nshow A ∨ ¬A\nbreak\n')
        self.assertTrue(result.ok)
        self.assertIsNone(result.proof_of('A ∨ ¬A'))
        self.assertFalse(result.proves('A ∨ ¬A'))

    def test_inside_a_block_is_not_at_the_top_level(self):
        result = kurt.check_text('load propositional\nprop A, B\nuse A\nassume B\n    A\n')
        self.assertTrue(result.complete)
        self.assertFalse(result.proves('A'))                           # (assumed, not proved)
        self.assertTrue(result.proves('B ⇒ A'))                        # the block's result is at the top level
        inner = kurt.check_text('load propositional\nprop A, B\nassume B\n    show B ∨ A\n    proof\n        B ∨ A\n    qed\n')
        self.assertTrue(inner.complete)
        self.assertIsNone(inner.proof_of('B ∨ A'))

    def test_a_loaded_fact_is_not_proved_here(self):
        with tempfile.TemporaryDirectory() as tmp:
            Path(tmp, 'helper.kurt').write_text('load propositional\nprop H\nuse H "h"\n', encoding='utf-8')
            main = Path(tmp, 'main.kurt')
            main.write_text('load helper\nshow H ∨ H\nproof\n    H ∨ H\nqed\n', encoding='utf-8')
            result = kurt.check_file(str(main))
            self.assertTrue(result.complete, result.error)
            self.assertEqual(result.proof_of('H'), 'loaded')
            self.assertFalse(result.proves('H'))
            self.assertTrue(result.proves('H ∨ H'))                    # derived here -- from the helper: see `loaded`
            self.assertEqual([os.path.basename(f) for f in result.loaded], ['propositional.kurt', 'helper.kurt'])
            self.assertTrue(all(os.path.isabs(f) for f in result.loaded))

    def test_an_empty_file_proves_nothing(self):
        result = kurt.check_text('')
        self.assertTrue(result.complete)                               # (why `complete` isn't enough for grading)
        self.assertFalse(result.proves('true'))
        self.assertEqual(result.loaded, [])

    def test_after_an_error(self):
        stopped = kurt.check_text('load propositional\nprop A, B\nuse A\nshow B\nproof\n    B\nqed\nA\n')
        self.assertFalse(stopped.ok)
        self.assertIsNone(stopped.proof_of('A'))                       # the check stopped: nothing is known
        self.assertEqual(stopped.loaded, [])
        all_errors = kurt.Session(kurt.RunConfig(all_errors=True))
        result = all_errors.check_text('load propositional\nprop A, B\nuse A\nshow B\nproof\n    B\nqed\nshow A ∨ B\nproof\n    A ∨ B\nqed\n')
        self.assertFalse(result.ok)
        self.assertEqual(result.proof_of('B'), 'admitted')             # admitted after its error
        self.assertTrue(result.proves('A ∨ B'))                        # (the file has an error, this claim a proof)

    def test_the_json_has_the_loaded_files_and_no_internals(self):
        import json
        data = json.loads(kurt.check_text(PROVED).to_json())
        self.assertEqual([os.path.basename(f) for f in data['loaded']], ['propositional.kurt'])
        self.assertFalse([key for key in data if key.startswith('_')])


SCENE = 'load propositional\nprop P, Q\nuse P ⇒ Q "pq"\n'
ANSWERS = 'load propositional\nprop P, Q, R\nuse P ∧ R ⇒ Q "a"\n'
EXERCISE = ('load theory/scene\nprop R\n\n; (a)\nshow P ∧ R ⇒ Q "a"   ; the label stays\nproof\n    todo\nqed\n\n'
            '; (b)\nshow P ⇒ Q ∨ R\nproof\n    todo\nqed\n')
SOLUTION = ('load theory/scene\nprop R\n\nshow P ∧ R ⇒ Q "a"\nproof\n    assume P ∧ R\n        P\n        Q\nqed\n\n'
            'show P ⇒ Q ∨ R\nproof\n    assume P\n        Q\n        Q ∨ R\nqed\n')


class TestGrader(unittest.TestCase):
    # scripts/grade_exercise.py on a small exercise of its own (the real ones: tests/test_exercises.py)

    def grade(self, solution_text: str, exercise_text: str = EXERCISE) -> tuple[bool, str]:
        with tempfile.TemporaryDirectory() as tmp:
            tmp = os.path.realpath(tmp)   # kurt resolves a loaded file's path; macOS's /tmp is a symlink
            theory = Path(tmp, 'exercise', 'theory')
            theory.mkdir(parents=True)
            (theory / 'scene.kurt').write_text(SCENE, encoding='utf-8')
            (theory / 'answers.kurt').write_text(ANSWERS, encoding='utf-8')     # (in the scene's directory, not loaded by the exercise)
            exercise = Path(tmp, 'exercise', '1-small.kurt')
            exercise.write_text(exercise_text, encoding='utf-8')
            solution = Path(tmp, 'solution.kurt')
            solution.write_text(solution_text, encoding='utf-8')
            return grade_exercise.grade(exercise, solution)

    def test_the_solution_is_complete(self):
        complete, report = self.grade(SOLUTION)
        self.assertTrue(complete, report)
        self.assertEqual(report.splitlines(), ['checked (strict)', 'proved: P ∧ R ⇒ Q "a"', 'proved: P ⇒ Q ∨ R'])

    def test_the_exercise_itself_is_not(self):
        complete, report = self.grade(EXERCISE)
        self.assertFalse(complete)
        self.assertIn('`todo` is not allowed', report)
        self.assertIn('admitted: P ∧ R ⇒ Q "a"', report)
        self.assertIn('admitted: P ⇒ Q ∨ R', report)

    def test_another_notation_lemmas_and_another_order_are_fine(self):
        solution = ('load theory/scene\nprop R\nshow P implies (Q or R)   ; (b) first\nproof\n    assume P\n        Q\n        Q ∨ R\nqed\n'
                    'show R ∧ P ⇒ P "lemma"\nproof\n    assume R ∧ P\n        P\nqed\n'
                    'show (R and P) implies Q "a"\nproof\n    assume R ∧ P\n        P\n        Q\nqed\n')
        complete, report = self.grade(solution)
        self.assertTrue(complete, report)

    def test_a_changed_statement_is_missing(self):
        complete, report = self.grade(SOLUTION.replace('show P ⇒ Q ∨ R', 'show P ⇒ Q ∨ R ∨ true'))
        self.assertFalse(complete)
        self.assertIn('missing: P ⇒ Q ∨ R', report)
        self.assertIn('proved: P ∧ R ⇒ Q "a"', report)

    def test_the_label_is_required(self):
        complete, report = self.grade(SOLUTION.replace(' "a"', ' "b"'))
        self.assertFalse(complete)
        self.assertIn('missing: P ∧ R ⇒ Q "a"', report)
        complete, report = self.grade(SOLUTION.replace(' "a"', ''))
        self.assertFalse(complete)
        self.assertIn('missing: P ∧ R ⇒ Q "a"', report)

    def test_a_todo_or_use_is_not_a_proof(self):
        complete, report = self.grade(SOLUTION.replace('        Q\n        Q ∨ R\n', '        todo\n        Q ∨ R\n'))
        self.assertFalse(complete)
        self.assertIn('`todo` is not allowed', report)
        self.assertIn('admitted: P ⇒ Q ∨ R', report)      # (the step after the dropped `todo` fails: admitted after its error)
        self.assertIn('proved: P ∧ R ⇒ Q "a"', report)
        complete, report = self.grade(SOLUTION.replace('show P ⇒ Q ∨ R\nproof\n    assume P\n        Q\n        Q ∨ R\nqed\n', 'use P ⇒ Q ∨ R\n'))
        self.assertFalse(complete)
        self.assertIn('`use` is not allowed', report)
        self.assertIn('missing: P ⇒ Q ∨ R', report)      # (dropped with its error)

    def test_a_withdrawn_claim_is_missing(self):
        complete, report = self.grade(SOLUTION.replace('show P ⇒ Q ∨ R\nproof\n    assume P\n        Q\n        Q ∨ R\nqed\n', 'show P ⇒ Q ∨ R\nbreak\n'))
        self.assertFalse(complete)
        self.assertIn('withdrew the claim', report)
        self.assertIn('missing: P ⇒ Q ∨ R', report)

    def test_a_proof_inside_a_block_does_not_count(self):
        solution = SOLUTION.replace('show P ⇒ Q ∨ R\nproof\n    assume P\n        Q\n        Q ∨ R\nqed\n',
                                    'assume R\n    show P ⇒ Q ∨ R\n    proof\n        assume P\n            Q\n            Q ∨ R\n    qed\n')
        complete, report = self.grade(solution)
        self.assertFalse(complete)
        self.assertIn('missing: P ⇒ Q ∨ R', report)

    def test_a_file_the_exercise_does_not_load_is_refused(self):
        solution = SOLUTION.replace('load theory/scene\nprop R\n', 'load theory/scene\nload theory/answers\n').replace(
            'show P ∧ R ⇒ Q "a"\nproof\n    assume P ∧ R\n        P\n        Q\nqed\n', 'P ∧ R ⇒ Q "a"\n')
        complete, report = self.grade(solution)
        self.assertFalse(complete)
        self.assertIn('loads `theory/answers.kurt`, which the exercise does not', report)
        self.assertIn('loaded: P ∧ R ⇒ Q "a"', report)       # (the answer, restated: not proved here)
        self.assertIn('checked (strict)', report)
        # proved from the loaded answer: a step of this file, but the loaded file gives it away
        complete, report = self.grade(solution.replace('P ∧ R ⇒ Q "a"\n', 'show P ∧ R ⇒ Q "a"\nproof\n    P ∧ R ⇒ Q\nqed\n'))
        self.assertFalse(complete)
        self.assertIn('loads `theory/answers.kurt`', report)
        self.assertIn('proved: P ∧ R ⇒ Q "a"', report)

    def test_an_exercise_that_does_not_check(self):
        complete, report = self.grade(SOLUTION, exercise_text=EXERCISE.replace('load theory/scene', 'load theory/missing'))
        self.assertFalse(complete)
        self.assertIn('the exercise itself does not check', report)


if __name__ == '__main__':
    unittest.main()
