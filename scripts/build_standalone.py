#!/usr/bin/env python3
"""Build a genuinely standalone `kurt.py`: `src/kurt/kurt.py` with every `theories/*.kurt`
file embedded directly in it (via `_EMBEDDED_THEORIES`, see kurt.py). The result is a single
file that can be downloaded on its own and immediately supports `load prop` (etc.) with no
`theories/` directory, no install, and no other files alongside it.

Usage:
    python3 scripts/build_standalone.py [-o OUTPUT]     # default: dist/kurt.py
"""
import argparse
import pprint
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SOURCE = REPO_ROOT / "src" / "kurt" / "kurt.py"
THEORIES_DIR = REPO_ROOT / "src" / "kurt" / "theories"
MARKER = "_EMBEDDED_THEORIES: dict[str, str] = {}"

def build(output: Path) -> None:
    source = SOURCE.read_text(encoding="utf-8")
    if source.count(MARKER) != 1:
        sys.exit(f"expected exactly one `{MARKER}` in {SOURCE}, found {source.count(MARKER)} -- "
                  f"has kurt.py's embedding hook changed shape? update this script's MARKER to match.")
    theories = {p.name: p.read_text(encoding="utf-8") for p in sorted(THEORIES_DIR.glob("*.kurt"))}
    if not theories:
        sys.exit(f"no `*.kurt` files found under {THEORIES_DIR}")
    embedded = f"_EMBEDDED_THEORIES: dict[str, str] = {pprint.pformat(theories)}"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(source.replace(MARKER, embedded), encoding="utf-8")
    output.chmod(0o755)
    print(f"wrote {output} ({output.stat().st_size:,} bytes, {len(theories)} embedded theories)")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("-o", "--output", type=Path, default=REPO_ROOT / "dist" / "kurt.py",
                         help="where to write the bundled file (default: dist/kurt.py)")
    args = parser.parse_args()
    build(args.output)
