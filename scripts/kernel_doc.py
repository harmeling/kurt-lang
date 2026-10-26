#!/usr/bin/env python3
"""The code chunks of a literate document, taken from src/kurt/kurt.py.

    python3 scripts/kernel_doc.py --check            # are the chunks of doc/kurt-kernel-code.md the code as it is?
    python3 scripts/kernel_doc.py --update           # write the chunks again from the code
    python3 scripts/kernel_doc.py --update doc/x.md  # another document

A document cites the code with a directive in an HTML comment, followed by a fenced ```python
block, which this script fills (and `--check`, run by tests/test_kernel_literate.py, compares):

    <!-- cite: def k_bound -->                      the top-level definition that starts with this prefix
    <!-- cite: class Certificate ... block: -->     from the line with the first prefix to the line with the second (inclusive)
    <!-- cite: kernel_verify :: case 'todo' ... case 'calc': -->   the same, searched inside the top-level definition `kernel_verify`

A prefix is matched against the stripped line; the first prefix must match exactly one line (of
the scope), the second the first line from there on. A top-level definition runs from its
`def`/`class` line (with a decorator before it) to the last line before the next line at column 0.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'src' / 'kurt' / 'kurt.py'
DOCUMENT = ROOT / 'doc' / 'kurt-kernel-code.md'
DIRECTIVE = re.compile(r'^<!-- cite: (.*?) -->\s*$')


def definitions(lines: list[str]) -> dict[str, tuple[int, int]]:
    # the top-level definitions: name -> (first line, last line), 0-based, inclusive
    found: dict[str, tuple[int, int]] = {}
    starts = [i for i, line in enumerate(lines) if re.match(r'(def|class) \w+', line)]
    for i in starts:
        declaration = re.match(r'(?:def|class) (\w+)', lines[i])
        assert declaration is not None          # (`starts` are the lines that match)
        name = declaration.group(1)
        first = i - 1 if i > 0 and lines[i - 1].startswith('@') else i
        last = i
        for j in range(i + 1, len(lines)):
            if lines[j] and not lines[j][0].isspace():
                break
            if lines[j].strip():
                last = j
        found.setdefault(name, (first, last))
    return found


def find_line(lines: list[str], prefix: str, lo: int, hi: int, where: str) -> int:
    hits = [i for i in range(lo, hi + 1) if lines[i].strip().startswith(prefix)]
    if len(hits) != 1:
        raise ValueError(f'the prefix `{prefix}` matches {len(hits)} lines {where}, not one')
    return hits[0]


def chunk(spec: str, lines: list[str], defs: dict[str, tuple[int, int]]) -> str:
    scope, _, rest = spec.partition(' :: ')
    if not rest:
        scope, rest = '', spec
    lo, hi, where = 0, len(lines) - 1, 'in kurt.py'
    if scope:
        if scope not in defs:
            raise ValueError(f'no top-level definition `{scope}`')
        lo, hi = defs[scope]
        where = f'in `{scope}`'
    first, _, last = rest.partition(' ... ')
    whole = re.fullmatch(r'(?:def|class) (\w+)', first.strip())
    if whole and not last and not scope:
        # a whole top-level definition, by its name
        if whole.group(1) not in defs:
            raise ValueError(f'no top-level definition `{whole.group(1)}`')
        start, end = defs[whole.group(1)]
        text = lines[start:end + 1]
        return '\n'.join(text)
    start = find_line(lines, first.strip(), lo, hi, where)
    if last:
        # the last line: the first line from the first one on that starts with the prefix
        end = next((i for i in range(start, hi + 1) if lines[i].strip().startswith(last.strip())), None)
        if end is None:
            raise ValueError(f'the prefix `{last.strip()}` matches no line after `{first.strip()}` {where}')
    else:
        name = re.match(r'(?:def|class) (\w+)', lines[start].strip())
        if name is None or lines[start][0].isspace():
            raise ValueError(f'`{first}` is not a top-level definition; give the last line too')
        start, end = defs[name.group(1)]
    text = lines[start:end + 1]
    indent = min(len(line) - len(line.lstrip()) for line in text if line.strip())
    return '\n'.join(line[indent:] if line.strip() else '' for line in text)


def process(document: Path, update: bool) -> list[str]:
    # the chunks that differ from the code (empty: up to date); with `update`, the document is rewritten
    lines = SOURCE.read_text(encoding='utf-8').split('\n')
    defs = definitions(lines)
    doc = document.read_text(encoding='utf-8').split('\n')
    out: list[str] = []
    stale: list[str] = []
    i = 0
    while i < len(doc):
        out.append(doc[i])
        directive = DIRECTIVE.match(doc[i])
        if directive:
            spec = directive.group(1)
            if i + 1 >= len(doc) or not doc[i + 1].startswith('```'):
                raise ValueError(f'line {i + 1}: a cite directive must be followed by a ``` block')
            fence = doc[i + 1]
            j = i + 2
            while j < len(doc) and doc[j] != '```':
                j += 1
            if j >= len(doc):
                raise ValueError(f'line {i + 2}: the ``` block is not closed')
            old = '\n'.join(doc[i + 2:j])
            new = chunk(spec, lines, defs)
            if old != new:
                stale.append(spec)
            out.append(fence)
            out.extend((new if update else old).split('\n'))
            out.append('```')
            i = j + 1
            continue
        i += 1
    if update:
        document.write_text('\n'.join(out), encoding='utf-8')
    return stale


def main(argv: list[str]) -> int:
    if len(argv) < 2 or argv[1] not in ('--check', '--update'):
        assert __doc__ is not None
        print(__doc__.strip().split('\n\n')[1])
        return 2
    document = Path(argv[2]) if len(argv) > 2 else DOCUMENT
    stale = process(document, update=argv[1] == '--update')
    if argv[1] == '--update':
        print(f'{document}: {len(stale)} chunk(s) written again' if stale else f'{document}: up to date')
        return 0
    for spec in stale:
        print(f'stale: <!-- cite: {spec} -->')
    print(f'{document}: {len(stale)} chunk(s) differ from the code -- run scripts/kernel_doc.py --update' if stale
          else f'{document}: every chunk is the code as it is')
    return 1 if stale else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
