#!/usr/bin/env python3
# Which members of `KbReader` (the type of the knowledge base in the kernel, the members of `KernelEnv`) does
# the type checker still need? For each member, a copy of `kurt.py` without it is checked by pyright:
# the errors that appear are the kernel functions (and the trusted functions they call) that use it.
# A member that no typed function needs is a candidate to leave out of both -- a smaller surface
# is less to trust; check it against what a run of the whole suite requests (the plan: git history of dev/todo-pyright.md).
#
#     python3 scripts/kernel_surface.py             # about 4 s per member, pyright must be installed
#     python3 scripts/kernel_surface.py --who       # also the functions that need each member
#
# Only code typed `KbReader` is checked (all of the kernel since `KernelEnv` is a `KbReader`).
import argparse
import json
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / 'src' / 'kurt' / 'kurt.py'


def check(directory: Path, lines: list[str]) -> list[dict]:
    (directory / 'kurt.py').write_text('\n'.join(lines), encoding='utf-8')
    run = subprocess.run(['pyright', '--outputjson'], cwd=directory, capture_output=True, text=True)
    return json.loads(run.stdout)['generalDiagnostics']


def enclosing_function(lines: list[str], index: int) -> str:
    while index > 0 and not lines[index].startswith('def '):
        index -= 1
    return lines[index].split('(')[0][4:]


def main() -> int:
    parser = argparse.ArgumentParser(description='the members of `KbReader` that typed kernel code needs')
    parser.add_argument('--who', action='store_true', help='also list the functions that need each member')
    args = parser.parse_args()
    lines = SOURCE.read_text(encoding='utf-8').split('\n')
    start = next(i for i, line in enumerate(lines) if line.startswith('class KbReader(Protocol):'))
    end = next(i for i, line in enumerate(lines) if i > start and line.startswith('class '))
    members = [m.group(1) for i in range(start, end) if (m := re.match(r'    def (\w+)\(self', lines[i]))]
    with tempfile.TemporaryDirectory() as tmp:
        directory = Path(tmp)
        (directory / 'pyrightconfig.json').write_text('{"pythonVersion": "3.10", "include": ["kurt.py"]}')
        baseline = Counter((x['range']['start']['line'], x['message'].split('\n')[0]) for x in check(directory, lines))
        needed: dict[str, list[str]] = {}
        for member in members:
            at = next(i for i in range(start, end) if re.match(rf'    def {member}\(self', lines[i]))
            gone = {at, at - 1} if lines[at - 1].strip() == '@property' else {at}
            without = [line for i, line in enumerate(lines) if i not in gone]
            added = []
            for x in check(directory, without):
                line = x['range']['start']['line']
                original = line + len(gone) if line >= at else line       # (the lines after the member moved up)
                if not baseline.get((original, x['message'].split('\n')[0])):
                    added.append(enclosing_function(without, line))
            needed[member] = added
    used = {m: sorted(set(f)) for m, f in needed.items() if f}
    print(f'{len(members)} members of KbReader; needed by typed code: {len(used)}')
    if args.who:
        for member, functions in used.items():
            print(f'  {member:24} {", ".join(functions[:6])}{" ..." if len(functions) > 6 else ""}')
    print('needed by no typed function:', ', '.join(m for m in members if m not in used) or 'none')
    return 0


if __name__ == '__main__':
    sys.exit(main())
