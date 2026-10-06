#!/usr/bin/env python3
# The speed of the search: check a few representative files one after the other (no `.kurtc`)
# and print the seconds of each -- before and after a change to the search, on a quiet machine
# (`uptime`), best of `--runs`.
#
#     python3 scripts/bench.py            # all
#     python3 scripts/bench.py --runs 3 natural field
import argparse
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FILES = {
    'natural': 'src/kurt/theories/natural.kurt',           # rules with schema conclusions, rewriting
    'analysis': 'src/kurt/theories/analysis.kurt',
    'group': 'src/kurt/theories/group.kurt',               # a flat operator variable
    'set': 'src/kurt/theories/set.kurt',
    'rational': 'src/kurt/theories/rational.kurt',
    'field': 'src/kurt/theories/field.kurt',           # many memberships, conditional rewriting
    'self-adjoint': 'proofs/mafi1/28-self-adjoint.kurt',   # lemmas with a general conclusion
    'contraposition': 'proofs/natural-deduction/contraposition.kurt',
    'cauchy-schwarz': 'proofs/linear-algebra/cauchy-schwarz.kurt',
}

def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('names', nargs='*', help=f'some of {", ".join(FILES)}')
    parser.add_argument('--runs', type=int, default=1)
    args = parser.parse_args()
    total = 0.0
    for name in args.names or FILES:
        best = None
        for _ in range(args.runs):
            start = time.perf_counter()
            done = subprocess.run([sys.executable, str(ROOT / 'src' / 'kurt' / 'kurt.py'), '--no-kurtc', str(ROOT / FILES[name])],
                                  capture_output=True, text=True, cwd=ROOT)
            seconds = time.perf_counter() - start
            best = seconds if best is None else min(best, seconds)
            if done.returncode != 0:
                print(f'{name}: FAILED\n{done.stderr[-500:]}')
        total += best
        print(f'{best:7.2f} s  {name}', flush=True)
    print(f'{total:7.2f} s  total')

if __name__ == '__main__':
    main()
