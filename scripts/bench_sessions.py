#!/usr/bin/env python3
# Cold loads and repeated sessions, apart: the time of `load rational` (and the theories below it)
# in a new `Session` -- cold, every theory checked from its source -- and of the same check again
# in the same session, where the theories come from its cache (as the editors and the playground
# check: one session, many checks). Also cold with the shipped certificates (`.kurtc`, as `kurt`
# on the command line loads). Best of `--runs`, on a quiet machine (`uptime`).
#
#     python3 scripts/bench_sessions.py             # rational
#     python3 scripts/bench_sessions.py --runs 3 natural field
import argparse
import contextlib
import io
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))
import kurt.kurt as kurt   # noqa: E402


def seconds(check) -> float:
    start = time.perf_counter()
    with contextlib.redirect_stdout(io.StringIO()):
        result = check()
    if not result.ok:
        sys.exit(f'FAILED: {result.error}')
    return time.perf_counter() - start


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('names', nargs='*', default=['rational'], help='theories to load (default: rational)')
    parser.add_argument('--runs', type=int, default=1)
    args = parser.parse_args()
    print(f'{"cold":>8} {"certified":>10} {"warm":>8}   theory      (seconds: a new session; a new session with the shipped .kurtc; the same session again)')
    for name in args.names:
        text = f'load {name}\n'
        cold = certified = warm = None
        for _ in range(args.runs):
            session = kurt.Session()                                   # no `.kurtc`: every theory checked from its source
            cold = min(filter(None, (cold, seconds(lambda: session.check_text(text)))))
            warm = min(filter(None, (warm, seconds(lambda: session.check_text(text)))))    # the same session: the theories from its cache
            with_kurtc = kurt.Session(kurt.RunConfig(kurtc=True))      # the certificates that come with Kurt
            certified = min(filter(None, (certified, seconds(lambda: with_kurtc.check_text(text)))))
        print(f'{cold:8.2f} {certified:10.2f} {warm:8.3f}   {name}', flush=True)


if __name__ == '__main__':
    main()
