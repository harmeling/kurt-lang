#!/usr/bin/env python3
"""Line coverage of src/kurt/kurt.py by the test suite, with the standard library only.

    python3 scripts/line_coverage.py            # percentage, then the missed lines per function
    python3 scripts/line_coverage.py --lines    # also print each missed line

Uses `sys.monitoring` (Python 3.12+), for machines where the `coverage` package isn't
installed. Tests that run Kurt in a subprocess (the CLI, the standalone bundle) aren't counted,
so `main` and the interactive shell show up as missed.
"""

import ast
import os
import sys
import types
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TARGET = os.path.join(ROOT, 'src', 'kurt', 'kurt.py')


def run_tests() -> set[int]:
    mon = sys.monitoring
    tool = mon.COVERAGE_ID
    mon.use_tool_id(tool, 'line_coverage')
    hit: set[int] = set()

    def on_line(code: types.CodeType, line: int):
        if code.co_filename == TARGET:
            hit.add(line)
        return mon.DISABLE              # each line is reported once

    mon.register_callback(tool, mon.events.LINE, on_line)
    mon.set_events(tool, mon.events.LINE)
    try:
        suite = unittest.defaultTestLoader.discover(os.path.join(ROOT, 'tests'), top_level_dir=ROOT)
        with open(os.devnull, 'w') as devnull:
            unittest.TextTestRunner(stream=devnull, verbosity=0).run(suite)
    finally:
        mon.set_events(tool, 0)
        mon.free_tool_id(tool)
    return hit


def executable_lines(src: str) -> set[int]:
    lines: set[int] = set()

    def walk(code: types.CodeType) -> None:
        lines.update(line for _, _, line in code.co_lines() if line is not None)
        for const in code.co_consts:
            if isinstance(const, types.CodeType):
                walk(const)

    walk(compile(src, TARGET, 'exec'))
    lines.discard(0)
    return lines


def ranges(numbers: list[int]) -> str:
    out = []
    start = prev = numbers[0]
    for n in numbers[1:] + [None]:
        if n is not None and n == prev + 1:
            prev = n
            continue
        out.append(f'{start}-{prev}' if start != prev else f'{start}')
        if n is not None:
            start = prev = n
    return ','.join(out)


def main() -> None:
    sys.path.insert(0, os.path.join(ROOT, 'src'))
    os.chdir(ROOT)
    hit = run_tests()
    src = open(TARGET).read()
    lines = executable_lines(src)
    missed = sorted(lines - hit)
    print(f'{len(lines) - len(missed)}/{len(lines)} lines = {100 * (len(lines) - len(missed)) / len(lines):.1f}%')

    functions = sorted((node.lineno, node.end_lineno, node.name) for node in ast.walk(ast.parse(src))
                       if isinstance(node, ast.FunctionDef))
    def owner(line: int) -> str:
        inner = [f for f in functions if f[0] <= line <= f[1]]
        return max(inner)[2] if inner else '<module>'
    by_function: dict[str, list[int]] = {}
    for line in missed:
        by_function.setdefault(owner(line), []).append(line)
    source = src.split('\n')
    for name, numbers in sorted(by_function.items(), key=lambda kv: -len(kv[1])):
        print(f'{len(numbers):4d}  {name:36s} {ranges(numbers)}')
        if '--lines' in sys.argv:
            for n in numbers:
                print(f'          {n:5d}  {source[n - 1].strip()[:100]}')


if __name__ == '__main__':
    main()
