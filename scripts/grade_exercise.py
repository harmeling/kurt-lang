#!/usr/bin/env python3
"""Grade a student's solution of an exercise of exercises/.

    python3 scripts/grade_exercise.py exercises/01-knights-and-knaves/2-two-islanders.kurt solution.kurt
    python3 scripts/grade_exercise.py --budget 60 EXERCISE SOLUTION     # 60 s of search per line (default 30)

The solution is checked as Kurt's `--strict` checks it (no `use`, `todo` or `chain`, every symbol
declared), with all its errors (`--all-errors`: an error doesn't stop the check, the claim stays
open), next to a copy of the exercise's own `theory/` directory, which is trusted (as with `-p`):
the student's file must prove everything from the scene, and from the theories that come with
Kurt. Then each top-level `show` of the exercise is looked up in the solution (`CheckResult.proof_of`,
in the solution's own notation: `A ⇒ B` and `A implies B` are the same statement, the order of the
statements doesn't matter): it is `proved` (a proof that rests on no `todo` and no error), or
`admitted` (a `todo` in its proof, an error), `assumed` (`use`), `loaded` (from a file, not proved
here), or `missing` (not stated at the top level, changed, or withdrawn with `break`); with the
exercise's label, if it has one. The solution may add lemmas of its own, and may load only what
the exercise loads (directly or through the scene): a file that states an answer is no proof.

Each line gets a budget of search time (`--budget SECONDS`, 30 by default, 0 for none): a line
that takes longer -- a false claim can take minutes -- fails with a `ResourceError`, which the
report shows apart from a rejection (the line is neither proved nor refuted; a larger budget may
decide it).

Prints what it found, and exits with 0 for a solution that is complete -- checked without an
error, every statement of the exercise proved, nothing else loaded -- and 1 otherwise.
"""
import argparse
import os
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


def required_statements(exercise_text: str) -> list[str]:
    # the top-level `show` lines of the exercise, as written (with their labels)
    return [line for line in top_level_lines(exercise_text) if line.startswith('show ')]


DEFAULT_BUDGET = 30.0      # seconds of search per line


def grade(exercise: Path, solution: Path, budget: float = DEFAULT_BUDGET) -> tuple[bool, str]:
    # (complete, report); `budget`: seconds of search per line, 0 for none
    theory = exercise.parent / 'theory'
    exercise_text = exercise.read_text(encoding='utf-8')
    solution_text = solution.read_text(encoding='utf-8')
    with tempfile.TemporaryDirectory() as tmp:
        tmp = os.path.realpath(tmp)   # kurt resolves a loaded file's path; macOS's /tmp is a symlink
        tmp_theory = Path(tmp) / 'theory'
        if theory.is_dir():
            shutil.copytree(theory, tmp_theory)
        else:
            tmp_theory.mkdir()
        checked = Path(tmp) / exercise.name
        # (only the scene and Kurt's theories, not the grader's directory)
        scene = (str(tmp_theory),)
        checked.write_text(exercise_text, encoding='utf-8')      # the exercise itself: what it loads
        given = kurt.check_file(str(checked), session=kurt.Session(kurt.RunConfig(paths=scene, search_cwd=False)))
        if not given.ok:
            return False, f'the exercise itself does not check: line {given.error_line}: {given.error}'
        checked.write_text(solution_text, encoding='utf-8')
        result = kurt.check_file(str(checked), session=kurt.Session(kurt.RunConfig(strict=True, all_errors=True, time_limit=budget or None, paths=scene, search_cwd=False)))
        extra = [os.path.relpath(f, tmp) for f in result.loaded if f not in given.loaded]
    report = []
    if result.exhausted:
        # (a budget is no verdict: said first, apart from a rejection)
        report.append(f'not decided: line {result.error_line} took more than {budget:g} s of search (the budget; `--budget` raises it)')
    if not result.ok:
        report.append(f'not checked: {len(result.errors)} error{"s" if len(result.errors) != 1 else ""}')
        report += [f'  line {e["line"]}: {e["message"].strip().splitlines()[-1]}'
                   for e in sorted(result.errors, key=lambda e: e['line'] or 0)]
    elif result.todos:
        report.append(f'not complete: {len(result.todos)} todo(s)')
        report += [f'  {todo}' for todo in result.todos]       # (a `todo`, or a claim withdrawn by `break`)
    else:
        report.append('checked (strict)')
    if extra:
        report.append(f'loads {", ".join(f"`{f}`" for f in extra)}, which the exercise does not -- not allowed')
    proved = []
    for statement in required_statements(exercise_text):
        status = result.proof_of(statement) or 'missing'
        proved.append(status == 'proved')
        report.append(f'{status}: {statement.removeprefix("show ")}')
    complete = result.complete and not extra and all(proved) and bool(proved)
    return complete, '\n'.join(report)


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=(__doc__ or '').strip().split('\n\n')[0], usage=(__doc__ or '').strip().split('\n\n')[1].strip())
    parser.add_argument('exercise', type=Path)
    parser.add_argument('solution', type=Path)
    parser.add_argument('--budget', type=float, default=DEFAULT_BUDGET, metavar='SECONDS',
                        help=f'the search time of one line (default {DEFAULT_BUDGET:g}; 0: no budget)')
    args = parser.parse_args(argv[1:])
    complete, report = grade(args.exercise, args.solution, budget=max(0.0, args.budget))
    print(report)
    print('COMPLETE' if complete else 'NOT COMPLETE')
    return 0 if complete else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
