#!/usr/bin/env python3
"""Grade a student's solution of an exercise of exercises/.

    python3 scripts/grade_exercise.py exercises/01-knights-and-knaves/2-two-islanders.kurt solution.kurt

The solution is checked as Kurt's `--strict` checks it (no `use`, `todo` or `chain`, every symbol
declared), next to a copy of the exercise's own `theory/` directory, which is trusted (as with
`-p`): the student's file must prove everything from the scene, and from the theories that come
with Kurt. Then its statements are compared with the exercise's: each top-level `show` of the
exercise must be in the solution, unchanged and in the same order (the solution may add lemmas of
its own), and so must the exercise's other top-level lines (`load`, `const`, `bool`, `def`, ...).

Prints what it found, and exits with 0 for a solution that is complete, 1 otherwise.
"""
import re
import shutil
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'src'))
import kurt.kurt as kurt   # noqa: E402

BLOCK_KEYWORDS = ('proof', 'qed')


def top_level_lines(text: str) -> list[str]:
    # the lines at the top level, without comments and with single spaces; a `show` with its
    # label, but not its `proof` ... `qed`
    lines = []
    for line in text.splitlines():
        if not line.strip() or line[0].isspace():
            continue
        code = re.sub(r'\s*;.*$', '', line).strip()
        if code and code not in BLOCK_KEYWORDS:
            lines.append(re.sub(r'\s+', ' ', code))
    return lines


def is_show(line: str) -> bool:
    return line.startswith('show ')


def compare_statements(exercise_text: str, solution_text: str) -> list[str]:
    # what of the exercise is missing or changed in the solution (empty: nothing)
    exercise, solution = top_level_lines(exercise_text), top_level_lines(solution_text)
    problems = []
    shows = [line for line in solution if is_show(line)]
    i = 0
    for line in exercise:
        if is_show(line):
            if line in shows[i:]:
                i = shows.index(line, i) + 1
            else:
                problems.append(f'the statement `{line}` is missing or changed (or not in the order of the exercise)')
        elif line not in solution:
            problems.append(f'the line `{line}` of the exercise is missing or changed')
    return problems


def grade(exercise: Path, solution: Path) -> tuple[bool, str]:
    # (complete, report)
    theory = exercise.parent / 'theory'
    with tempfile.TemporaryDirectory() as tmp:
        tmp_theory = Path(tmp) / 'theory'
        if theory.is_dir():
            shutil.copytree(theory, tmp_theory)
        else:
            tmp_theory.mkdir()
        checked = Path(tmp) / exercise.name
        solution_text = solution.read_text(encoding='utf-8')
        checked.write_text(solution_text, encoding='utf-8')
        session = kurt.Session(kurt.RunConfig(strict=True, paths=(str(tmp_theory),)))
        result = kurt.check_file(str(checked), session=session)
    problems = compare_statements(exercise.read_text(encoding='utf-8'), solution_text)
    report = []
    if not result.ok:
        report.append(f'not checked: line {result.error_line}: {result.error}')
    elif result.todos:
        report.append(f'not complete: {len(result.todos)} todo(s)')
    else:
        report.append('checked (strict)')
    report += problems
    return result.complete and not problems, '\n'.join(report)


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print(__doc__.strip().split('\n\n')[1])
        return 2
    complete, report = grade(Path(argv[1]), Path(argv[2]))
    print(report)
    print('COMPLETE' if complete else 'NOT COMPLETE')
    return 0 if complete else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
