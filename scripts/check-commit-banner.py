#!/usr/bin/env python3
import re, subprocess, sys, pathlib

FILE = pathlib.Path("kurt.py")

try:
    head = subprocess.check_output(
        ["git", "rev-parse", "--short=12", "HEAD"], text=True
    ).strip()
except Exception as e:
    print("⚠️  Could not determine git commit:", e, file=sys.stderr)
    sys.exit(0)  # don't fail

text = FILE.read_text(encoding="utf-8")

m = re.search(r"COMMIT\s*=\s*['\"]([^'\"]+)['\"]", text)
if not m:
    print("⚠️  No COMMIT variable found in kurt.py", file=sys.stderr)
    sys.exit(0)

commit_in_file = m.group(1)
if commit_in_file != head:
    print(f"⚠️  kurt.py banner commit is '{commit_in_file}', "
          f"but HEAD is '{head}'.", file=sys.stderr)
    print("   Did you forget to run ./scripts/install-hooks.sh ?", file=sys.stderr)
    sys.exit(0)
