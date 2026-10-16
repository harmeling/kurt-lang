#!/usr/bin/env python3
"""Build a genuinely standalone `kurt.py`: `src/kurt/kurt.py` with every `theories/*.kurt`
file embedded directly in it (via `_EMBEDDED_THEORIES`, see kurt.py), together with their
certificates (`_EMBEDDED_CERTIFICATES`, made by `scripts/build_certificates.py` first). The result
is a single file that can be downloaded on its own and immediately supports `load prop` (etc.)
with no `theories/` directory, no install, and no other files alongside it.

Usage:
    python3 scripts/build_standalone.py [-o OUTPUT]     # default: dist/kurt.py
"""
import argparse
import base64
import json
import zlib
import pprint
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
SOURCE = REPO_ROOT / "src" / "kurt" / "kurt.py"
THEORIES_DIR = REPO_ROOT / "src" / "kurt" / "theories"
MARKER = "_EMBEDDED_THEORIES: dict[str, str] = {}"
CERTIFICATES_MARKER = "_EMBEDDED_CERTIFICATES: dict[str, str] = {}"

def build(output: Path) -> None:
    source = SOURCE.read_text(encoding="utf-8")
    for marker in (MARKER, CERTIFICATES_MARKER):
        if source.count(marker) != 1:
            sys.exit(f"expected exactly one `{marker}` in {SOURCE}, found {source.count(marker)} -- "
                      f"has kurt.py's embedding hook changed shape? update this script's markers to match.")
    theories = {p.name: p.read_text(encoding="utf-8") for p in sorted(THEORIES_DIR.glob("*.kurt"))}
    if not theories:
        sys.exit(f"no `*.kurt` files found under {THEORIES_DIR}")
    sys.path.insert(0, str(REPO_ROOT / "scripts"))
    import build_certificates
    build_certificates.build()           # (up to date: only what changed is checked again)
    certificates = {}
    for name in theories:
        kurtc = THEORIES_DIR / (name + "c")
        if kurtc.is_file():
            json.loads(kurtc.read_text(encoding="utf-8"))        # (not damaged)
            certificates[name] = base64.b64encode(zlib.compress(kurtc.read_bytes(), 9)).decode("ascii")
    embedded = f"_EMBEDDED_THEORIES: dict[str, str] = {pprint.pformat(theories)}"
    embedded_certificates = f"_EMBEDDED_CERTIFICATES: dict[str, str] = {pprint.pformat(certificates)}"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(source.replace(MARKER, embedded).replace(CERTIFICATES_MARKER, embedded_certificates), encoding="utf-8")
    output.chmod(0o755)
    print(f"wrote {output} ({output.stat().st_size:,} bytes, {len(theories)} embedded theories, {len(certificates)} with certificates)")

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("-o", "--output", type=Path, default=REPO_ROOT / "dist" / "kurt.py",
                         help="where to write the bundled file (default: dist/kurt.py)")
    args = parser.parse_args()
    build(args.output)
