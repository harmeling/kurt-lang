#!/usr/bin/env python3
"""The axioms of the theories that come with Kurt (dev/todo.md 11, doc/kurt-soundness.md §11).

For each theory: its `use` lines (axioms: admitted, not proved), its `def`s (conservative
definitions, checked) and its `show`s (theorems, proved in Kurt). An axiom with a `lean "label"
TACTIC` line is proved in Lean as well (`kurt --lean`, tests/test_export_lean.py), in the model of
the Lean export; the others are listed, to be justified in doc/kurt-soundness.md §11.

usage: python3 scripts/axiom_audit.py [--list]      (--list: every axiom without a Lean proof)
"""
import re
import sys
from pathlib import Path

THEORIES = Path(__file__).resolve().parent.parent / 'src' / 'kurt' / 'theories'


def audit(path: Path) -> dict:
    text = path.read_text(encoding='utf-8')
    uses = re.findall(r'^\s*use .*?"([^"]+)"\s*(?:;.*)?$', text, re.MULTILINE)
    unlabelled = [l for l in re.findall(r'^\s*use (.*)$', text, re.MULTILINE) if '"' not in l]
    lean = set(re.findall(r'^lean "([^"]+)"', text, re.MULTILINE))
    return {
        'use': len(uses) + len(unlabelled),
        'def': len(re.findall(r'^\s*def ', text, re.MULTILINE)),
        'show': len(re.findall(r'^\s*show ', text, re.MULTILINE)),
        'lean': len([u for u in uses if u in lean]),
        'unproved': [u for u in uses if u not in lean] + [f'(no label) {l.strip()[:60]}' for l in unlabelled],
    }


def main() -> None:
    listing = '--list' in sys.argv
    print(f'{"theory":14} {"use":>4} {"lean":>5} {"def":>4} {"show":>5}  axioms without a Lean proof')
    for path in sorted(THEORIES.glob('*.kurt')):
        if path.name == 'minimal.kurt':
            continue
        a = audit(path)
        print(f'{path.stem:14} {a["use"]:>4} {a["lean"]:>5} {a["def"]:>4} {a["show"]:>5}  {len(a["unproved"])}')
        if listing:
            for label in a['unproved']:
                print(f'{"":16}- {label}')


if __name__ == '__main__':
    main()
