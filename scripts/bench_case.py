#!/usr/bin/env python3
# The runtime of n-ary `case` (dev/todo.md, item 2): for n alternatives `A1 or ... or An`, the goal
# `G` from one implication per alternative -- written directly (`use Ai implies G`) or as real
# `case Ai` blocks -- with n unrelated disjunctions and implications in scope. For each n: the time
# of a fresh process, the time of a check in a session and of the same check again in that
# session, the calls of the general search (`impl_elim`), and the rule of the final step (it must
# be `case-elim`, not a combination found by the general search). On a quiet machine (`uptime`).
#
#     python3 scripts/bench_case.py                  # n = 2, 4, ..., 128
#     python3 scripts/bench_case.py --sizes 2 4 8 --runs 3
import argparse
import contextlib
import io
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))
import kurt.kurt as kurt    # noqa: E402


def source(n: int, variant: str) -> str:
    alts = [f'A{i}' for i in range(n)]
    noise = [(f'B{j}', f'C{j}', f'H{j}') for j in range(n)]
    lines = ['load prop',
             'bool ' + ', '.join(alts + ['G', 'K'] + [s for t in noise for s in t]),
             'use ' + ' or '.join(alts)]
    for b, c, h in noise:            # unrelated: a disjunction, and its cases for another goal
        lines += [f'use {b} or {c}', f'use {b} implies {h}', f'use {c} implies {h}']
    if variant == 'direct':
        lines += [f'use {a} implies G' for a in alts]
        lines += ['G']
    else:                            # each block derives `G` inside: `Ai implies G` isn't a fact
        lines += ['use K'] + [f'use {a} and K implies G' for a in alts]
        for a in alts:
            lines += [f'case {a}', '    G']
        lines += ['G']
    return '\n'.join(lines) + '\n'


def cold(path: Path) -> float:
    start = time.perf_counter()
    done = subprocess.run([sys.executable, str(ROOT / 'src' / 'kurt' / 'kurt.py'), '--no-kurtc', str(path)],
                          capture_output=True, text=True)
    seconds = time.perf_counter() - start
    if done.returncode != 0:
        raise SystemExit(f'{path.name}: FAILED\n{done.stderr[-800:]}')
    return seconds


def in_session(text: str) -> tuple[float, float, int, float, str]:
    # a check, and the same check again in the same session; the calls of `impl_elim` and the
    # seconds in `nary_case_elim` in the first; the reason of the last line
    calls, case_seconds = [0], [0.0]
    original, original_case = kurt.impl_elim, kurt.nary_case_elim
    def counted(*args, **kwargs):
        calls[0] += 1
        return original(*args, **kwargs)
    def timed(*args, **kwargs):
        start = time.perf_counter()
        try:
            return original_case(*args, **kwargs)
        finally:
            case_seconds[0] += time.perf_counter() - start
    session = kurt.new_session(kurt.RunConfig())
    kurt.impl_elim, kurt.nary_case_elim = counted, timed
    try:
        start = time.perf_counter()
        first = session.check_text(text, name='bench.kurt')
        t1 = time.perf_counter() - start
    finally:
        kurt.impl_elim, kurt.nary_case_elim = original, original_case
    start = time.perf_counter()
    session.check_text(text, name='bench.kurt')
    t2 = time.perf_counter() - start
    if not first.ok:
        raise SystemExit(f'session check failed: {first.error}')
    last = [line for line in first.output.splitlines() if line.startswith('G ')][-1]
    return t1, t2, calls[0], case_seconds[0], last.split(';', 1)[1].strip()


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--sizes', type=int, nargs='*', default=[2, 4, 8, 16, 32, 64, 128])
    parser.add_argument('--runs', type=int, default=1, help='best of RUNS for the times')
    parser.add_argument('--variants', nargs='*', default=['direct', 'blocks'])
    args = parser.parse_args()
    print(f'{"variant":8s} {"n":>4s} {"cold s":>8s} {"session s":>10s} {"again s":>8s} {"impl_elim":>10s} {"case-elim s":>12s}  final step')
    with tempfile.TemporaryDirectory() as tmp:
        for variant in args.variants:
            for n in args.sizes:
                text = source(n, variant)
                path = Path(tmp) / f'case-{variant}-{n}.kurt'
                path.write_text(text)
                c = min(cold(path) for _ in range(args.runs))
                runs = [in_session(text) for _ in range(args.runs)]
                t1 = min(r[0] for r in runs)
                t2 = min(r[1] for r in runs)
                calls, case_s, step = runs[0][2], min(r[3] for r in runs), runs[0][4]
                rule = step.split('(')[0]
                print(f'{variant:8s} {n:4d} {c:8.2f} {t1:10.2f} {t2:8.2f} {calls:10d} {case_s:12.4f}  {rule}', flush=True)
                if 'case-elim' not in step:
                    print(f'  ! the final step is not case-elim: {step}')


if __name__ == '__main__':
    with contextlib.suppress(KeyboardInterrupt):
        main()
