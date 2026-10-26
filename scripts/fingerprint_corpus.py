#!/usr/bin/env python3
# What the checker says about every `.kurt` file of the repository, as one hash per file: whether it
# is ok, its output, its error, the long form of the certificates of every line, its `todo`s. Run it
# before and after a change that must not change what Kurt accepts or says (a refactoring, a typing
# change, a narrower `KbReader`), and compare:
#
#     python3 scripts/fingerprint_corpus.py before.json
#     ... change something ...
#     python3 scripts/fingerprint_corpus.py after.json
#     python3 scripts/fingerprint_corpus.py --compare before.json after.json
#
# `--root DIR` takes the files and the `src/kurt` of another copy of the repository (to try a change
# on a copy). About 5 minutes on four cores. Sensitive: a kernel that can't read one member it needs
# changes most files (checked when `KbReader` was narrowed; the plan: git history of dev/todo-pyright.md).
import argparse
import glob
import hashlib
import json
import multiprocessing
import os
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DIRECTORIES = ('proofs', 'tutorial', 'keywords', 'exercises', 'src/kurt/theories', 'tests')


def fingerprint(job: tuple[str, str]) -> tuple[str, str]:
    root, path = job
    source = os.path.join(root, 'src')
    if source not in sys.path:
        sys.path.insert(0, source)          # (a worker starts fresh, on macOS: the copy's own `kurt`)
    import kurt
    try:
        result = kurt.Session().check_file(path, certificates=True)
        text = json.dumps([result.ok, result.output, result.error, result.error_kind, result.error_line,
                           sorted(result.certificates.items()), result.todos], default=str, sort_keys=True)
    except Exception as e:                  # (a crash is a result too)
        text = f'CRASH {type(e).__name__}: {e}'
    return os.path.relpath(path, root), hashlib.sha256(text.encode('utf-8')).hexdigest()


def compare(before: Path, after: Path) -> int:
    a, b = json.loads(before.read_text()), json.loads(after.read_text())
    different = sorted(name for name in a.keys() & b.keys() if a[name] != b[name])
    only = sorted(a.keys() ^ b.keys())
    print(f'{len(a.keys() & b.keys())} files compared, {len(different)} different, {len(only)} in only one')
    for name in different + only:
        print(f'  {name}')
    return 1 if different or only else 0


def main() -> int:
    parser = argparse.ArgumentParser(description='a hash of what the checker says, per `.kurt` file')
    parser.add_argument('output', nargs='?', help='where to write the hashes (JSON)')
    parser.add_argument('--compare', nargs=2, metavar=('BEFORE', 'AFTER'), help='compare two runs')
    parser.add_argument('--root', default=str(ROOT), help='the repository to check (default: this one)')
    parser.add_argument('--jobs', type=int, default=4)
    args = parser.parse_args()
    if args.compare:
        return compare(Path(args.compare[0]), Path(args.compare[1]))
    if args.output is None:
        parser.error('an output file, or --compare BEFORE AFTER')
    root = os.path.abspath(args.root)
    files = [path for directory in DIRECTORIES
             for path in sorted(glob.glob(os.path.join(root, directory, '**', '*.kurt'), recursive=True))]
    with multiprocessing.Pool(args.jobs) as pool:
        found = dict(pool.map(fingerprint, [(root, path) for path in files], chunksize=4))
    Path(args.output).write_text(json.dumps(found, indent=0, sort_keys=True))
    print(f'{len(found)} files fingerprinted')
    return 0


if __name__ == '__main__':
    sys.exit(main())
