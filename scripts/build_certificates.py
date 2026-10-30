#!/usr/bin/env python3
"""Check every theory of `src/kurt/theories/` and write its certificates (`theories/*.kurtc`), so
that they can be shipped: the standalone `kurt.py` embeds them (`scripts/build_standalone.py`),
and the package has them next to the theories (`pyproject.toml`). A bundled or installed Kurt
can't write certificates next to its theories, and without them it checks natural.kurt
and divisibility.kurt from scratch on every `load` (seconds each time). The kernel
checks a shipped certificate again, as any other: it only saves the search.

Usage:
    python3 scripts/build_certificates.py
"""
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
THEORIES_DIR = REPO_ROOT / "src" / "kurt" / "theories"
sys.path.insert(0, str(REPO_ROOT / "src"))

import json     # noqa: E402
import kurt     # noqa: E402  (the one of this repository)
import kurt.kurt as internals     # noqa: E402


def up_to_date(theory: Path) -> bool:
    # its certificates are for the theory as it is, and for the theories it loads as they are
    try:
        content = json.loads(theory.with_name(theory.name + "c").read_text(encoding="utf-8"))
        return (content["kurtc"] == internals.KURTC_VERSION and content["sha256"] == internals.source_hash(str(theory))
                and all(d["sha256"] == internals.source_hash(internals.local_file(d["file"])) for d in content["depends"]))
    except (OSError, ValueError, KeyError, TypeError):
        return False


def build() -> list[Path]:
    session = kurt.new_session(kurt.RunConfig(kurtc=True))
    written = []
    for theory in sorted(THEORIES_DIR.glob("*.kurt")):
        if theory.name == "minimal.kurt":       # the core: read when Kurt starts, never loaded
            continue
        if up_to_date(theory):
            written.append(theory.with_name(theory.name + "c"))
            continue
        result = session.check_file(str(theory))
        if not result.ok:
            sys.exit(f"{theory.name} doesn't check: {result.error}")
        kurtc = theory.with_name(theory.name + "c")
        if not kurtc.is_file():
            sys.exit(f"no certificates written for {theory.name}")
        written.append(kurtc)
    return written


if __name__ == "__main__":
    print(f"certificates of {len(build())} theories in {THEORIES_DIR}")
