import os
import sys
import unittest
import concurrent.futures
from pathlib import Path

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

sys.path.insert(0, str(PROJECT_ROOT / 'scripts'))
import grade_exercise   # noqa: E402
sys.path.remove(str(PROJECT_ROOT / 'scripts'))   # (only needed for the import above, not left on sys.path for the rest of the suite)

# exercises/TOPIC/ has the exercises of a topic (`*.kurt`, with `todo`s for the student) and their
# scene in TOPIC/theory/. Each theory must check completely, each exercise must check with its
# `todo`s left. The solutions are in dev/exercise-solutions/TOPIC/ (not published): each must be
# complete as `scripts/grade_exercise.py` grades it -- strict, and with the statements of the
# exercise.

EXERCISES = PROJECT_ROOT / 'exercises'
SOLUTIONS = PROJECT_ROOT / 'dev' / 'exercise-solutions'
JOBS = int(os.environ.get('KURT_TEST_JOBS', '4'))


def topics() -> list[Path]:
    return sorted(p for p in EXERCISES.iterdir() if p.is_dir())


def exercises() -> list[Path]:
    return [p for t in topics() for p in sorted(t.glob('*.kurt'))]


def check(path: str) -> tuple[bool, int, str]:
    # (ok, number of todos, error)
    result = kurt.check_file(path)
    return result.ok, len(result.todos), result.error or ''


def grade(names: tuple[str, str]) -> tuple[bool, str]:
    return grade_exercise.grade(Path(names[0]), Path(names[1]))


def run(f, items):
    if JOBS > 1:
        with concurrent.futures.ProcessPoolExecutor(max_workers=JOBS) as pool:
            return list(pool.map(f, items, chunksize=1))
    return [f(i) for i in items]


class TestExercises(unittest.TestCase):
    def test_each_topic_has_a_theory_and_exercises(self):
        self.assertTrue(topics())
        for topic in topics():
            with self.subTest(topic=topic.name):
                self.assertTrue(list((topic / 'theory').glob('*.kurt')), 'no scene in theory/')
                self.assertTrue(list(topic.glob('*.kurt')), 'no exercises')

    def test_theories_check(self):
        theories = [str(p) for t in topics() for p in sorted((t / 'theory').glob('*.kurt'))]
        for name, (ok, todos, error) in zip(theories, run(check, theories)):
            with self.subTest(theory=name):
                self.assertTrue(ok, error)
                self.assertEqual(todos, 0)

    def test_exercises_check_with_todos(self):
        names = [str(p) for p in exercises()]
        for name, (ok, todos, error) in zip(names, run(check, names)):
            with self.subTest(exercise=name):
                self.assertTrue(ok, error)
                self.assertGreater(todos, 0, 'an exercise leaves something to do')

    @unittest.skipUnless(SOLUTIONS.is_dir(), 'the solutions are not published')
    def test_solutions_are_complete(self):
        pairs = []
        for exercise in exercises():
            solution = SOLUTIONS / exercise.parent.name / exercise.name
            with self.subTest(exercise=str(exercise)):
                self.assertTrue(solution.is_file(), f'no solution {solution}')
            if solution.is_file():
                pairs.append((str(exercise), str(solution)))
        for (exercise, _), (complete, report) in zip(pairs, run(grade, pairs)):
            with self.subTest(solution=exercise):
                self.assertTrue(complete, report)


class TestGrading(unittest.TestCase):
    exercise = EXERCISES / '01-knights-and-knaves' / '1-truth-and-lies.kurt'

    def test_the_exercise_itself_is_not_complete(self):
        complete, report = grade_exercise.grade(self.exercise, self.exercise)
        self.assertFalse(complete)
        self.assertIn('todo', report)    # strict: a `todo` is an error
        self.assertIn('admitted: ¬(A says knave(A))', report)    # each statement, with how it stands

    def test_a_changed_statement_is_missing(self):
        # the statements are compared as Kurt reads them (tests/test_grading.py has the small cases)
        import tempfile
        text = self.exercise.read_text(encoding='utf-8')
        changed = text.replace('show ¬(A says knave(A))', 'show ¬(A says knave(A)) ∨ true')
        self.assertNotEqual(text, changed)
        with tempfile.TemporaryDirectory() as tmp:
            solution = Path(tmp) / 'solution.kurt'
            solution.write_text(changed, encoding='utf-8')
            complete, report = grade_exercise.grade(self.exercise, solution)
        self.assertFalse(complete)
        self.assertIn('missing: ¬(A says knave(A))', report)
        self.assertEqual(report.count('missing:'), 1)

    def test_an_axiom_of_the_student_is_refused(self):
        import tempfile
        text = self.exercise.read_text(encoding='utf-8')
        cheat = text.replace('const A\n', 'const A\nuse ¬(A says knave(A))\n', 1)
        with tempfile.TemporaryDirectory() as tmp:
            solution = Path(tmp) / 'solution.kurt'
            solution.write_text(cheat, encoding='utf-8')
            complete, report = grade_exercise.grade(self.exercise, solution)
        self.assertFalse(complete)
        self.assertIn('`use` is not allowed', report)

    def test_a_withdrawn_claim_is_not_complete(self):
        # `show X`, `break` for every claim: no `todo`, no `use`, nothing open -- COMPLETE (2026-10-15,
        # found by the boundary hunt); a withdrawn claim is a `todo` now
        import re
        import tempfile
        text = self.exercise.read_text(encoding='utf-8')
        cheat = re.sub(r'\nproof\n(    .*\n)+qed\n', '\nbreak\n', text)
        self.assertNotIn('\nproof\n', cheat)
        with tempfile.TemporaryDirectory() as tmp:
            solution = Path(tmp) / 'solution.kurt'
            solution.write_text(cheat, encoding='utf-8')
            complete, report = grade_exercise.grade(self.exercise, solution)
        self.assertFalse(complete)
        self.assertIn('not complete', report)
        self.assertIn('withdrew the claim', report)

    def test_the_grader_does_not_search_its_working_directory(self):
        # a graded file found `.kurt` files where the teacher ran the grader (todo 46, 2026-10-15)
        import tempfile
        text = self.exercise.read_text(encoding='utf-8')
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / 'helper.kurt').write_text('load propositional\nprop H\nuse H "h"\n', encoding='utf-8')
            solution = Path(tmp) / 'solution.kurt'
            solution.write_text(text.replace('load theory/island\n', 'load theory/island\nload helper\n', 1), encoding='utf-8')
            cwd = os.getcwd()
            os.chdir(tmp)
            try:
                complete, report = grade_exercise.grade(self.exercise, solution)
            finally:
                os.chdir(cwd)
        self.assertFalse(complete)
        self.assertIn('unable to open `helper.kurt`', report)


if __name__ == '__main__':
    unittest.main()
