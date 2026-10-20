#!/usr/bin/env python3
"""Check a `kurt --lean` export with Lean -- with Mathlib if the file imports it.

    python3 scripts/lean_check.py proof.lean [more.lean ...]

A file with `import Mathlib` (an export of a proof that loads a number theory, see doc/kurt-doc.md,
`--lean`) is checked by `lake env lean` in the lake project scripts/lean (or $KURT_MATHLIB_PROJECT),
which must be set up once:

    cd scripts/lean && lake exe cache get      # Mathlib's prebuilt oleans, into scripts/lean/.lake

Any other file by plain `lean`. The exit status is Lean's (the largest over the files); Lean's
output is printed. Neither Kurt nor `pip install kurt-lang` needs any of this.
"""
import os
import shutil
import subprocess
import sys
from pathlib import Path

PROJECT = Path(os.environ.get('KURT_MATHLIB_PROJECT') or Path(__file__).resolve().parent / 'lean')


def elan_tool(name: str) -> str | None:
    found = shutil.which(name)
    if found:
        return found
    candidate = Path.home() / '.elan' / 'bin' / name
    return str(candidate) if candidate.is_file() else None


def mathlib_ready(project: Path = PROJECT) -> bool:
    # the project is set up: Mathlib checked out with its oleans (`lake exe cache get`)
    mathlib = project / '.lake' / 'packages' / 'mathlib'
    return (project / 'lakefile.toml').is_file() and (mathlib / '.lake' / 'build' / 'lib' / 'lean' / 'Mathlib.olean').is_file()


def lean_command(path: Path, project: Path = PROJECT) -> tuple[list[str], Path]:
    # the command that checks `path`, and where it runs
    uses_mathlib = any(line.strip() == 'import Mathlib' for line in path.read_text(encoding='utf-8').splitlines()[:5])
    if uses_mathlib:
        lake = elan_tool('lake')
        if lake is None or not mathlib_ready(project):
            raise SystemExit(f'{path}: imports Mathlib, but the lake project {project} is not set up '
                             f'(cd {project} && lake exe cache get; see doc/kurt-doc.md, `--lean`)')
        return [lake, 'env', 'lean', str(path.resolve())], project
    lean = elan_tool('lean')
    if lean is None:
        raise SystemExit('Lean is not installed (see scripts/lean-toolchain)')
    return [lean, path.name], path.resolve().parent


def main(argv: list[str]) -> int:
    if not argv or argv[0] in ('-h', '--help'):
        print(__doc__)
        return 0 if argv else 2
    status = 0
    for name in argv:
        command, cwd = lean_command(Path(name))
        result = subprocess.run(command, cwd=cwd)
        status = max(status, result.returncode)
    return status


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
