#!/usr/bin/env python3
"""Turn Kurt's output for a proof file into a LaTeX document.

    python3 scripts/kurt2latex.py path/to/proof.kurt > proof.tex    # runs `kurt` on the file
    kurt path/to/proof.kurt | python3 scripts/kurt2latex.py -       # or reads its output

Each line of Kurt's output (`formula ; reason`, indented by the nesting of blocks) becomes a
row of a two-column table: the formula in math mode, with keywords and symbols replaced by
LaTeX macros (see `SYMBOLS`), and the reason next to it. This is formatting only -- it is not
part of Kurt itself.
"""

import re
import subprocess
import sys
from pathlib import Path

HEADER = r'''\documentclass{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{amsmath,amssymb}
\usepackage{array}
\usepackage[a4paper, hmargin={3.5cm,3cm}, vmargin={2cm,2cm}]{geometry}
\usepackage{stmaryrd}

\newcolumntype{L}[1]{>{\raggedright\arraybackslash}p{#1}}

\begin{document}

\begin{flushleft}
\begin{tabular}{L{0.45\linewidth} L{0.45\linewidth}}
'''

FOOTER = r'''\end{tabular}
\end{flushleft}
\end{document}
'''

# keywords and symbols of Kurt and its theories, and how to write them in LaTeX
SYMBOLS = {
    # keywords
    'assume': r'\text{Assume that }', 'case': r'\text{Case }', 'let': r'\text{Let }',
    'pick': r'\text{Pick }', 'show': r'\text{To show: }', 'proof': r'\textbf{proof}',
    'qed': r'\textbf{qed}', 'with': r'\text{ with }', 'use': r'\text{use }', 'load': r'\text{load }',
    # logic
    'implies': r'\Rightarrow', '⇒': r'\Rightarrow', 'and': r'\land', '∧': r'\land',
    'or': r'\lor', '∨': r'\lor', 'not': r'\lnot', '¬': r'\lnot', 'iff': r'\Leftrightarrow',
    '⇔': r'\Leftrightarrow', '≡': r'\equiv', 'forall': r'\forall', '∀': r'\forall',
    'exists': r'\exists', '∃': r'\exists', 'true': r'\text{true}', '⊤': r'\top',
    'false': r'\text{false}', '⊥': r'\bot', 'contradiction': r'\text{contradiction}',
    # relations, sets, arithmetic
    '≠': r'\neq', '<=': r'\leq', '≤': r'\leq', '>=': r'\geq', '≥': r'\geq', 'in': r'\in',
    '∈': r'\in', '⊂': r'\subset', '∪': r'\cup', '∩': r'\cap', '∅': r'\emptyset',
    '→': r'\to', '*': r'\cdot', '□': r'\Box', '◇': r'\Diamond', 'λ': r'\lambda',
}

LINE = re.compile(r'^( *)(.*?)\s*(?:; (.*))?$')


def latex_formula(text: str) -> str:
    text = text.replace('%', r'\%').replace('$', r'\$')
    words = re.split(r'(\s+|[(){}\[\],])', text)
    return ''.join(SYMBOLS.get(w, w) for w in words)


def latex_document(output: str, indent: int = 4) -> str:
    rows = []
    for line in output.splitlines():
        if line.startswith('This is Kurt') or line.strip() == '':
            continue
        match = LINE.match(line)
        assert match is not None
        spaces, formula, reason = match.groups()
        if formula.startswith(';') or formula.startswith('Proof'):
            rows.append(f'% {line}')      # a note or the final verdict, kept as a comment
            continue
        quads = r'\quad' * (len(spaces) // indent)
        reason = (reason or '').replace('%', r'\%').replace('_', r'\_')
        rows.append(f'${quads} {latex_formula(formula)}$ & {reason} \\\\')
    return HEADER + '\n'.join(rows) + '\n' + FOOTER


def main() -> None:
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    if sys.argv[1] == '-':
        output = sys.stdin.read()
    else:
        kurt = Path(__file__).resolve().parent.parent / 'src' / 'kurt' / 'kurt.py'
        result = subprocess.run([sys.executable, str(kurt), sys.argv[1]], capture_output=True, text=True)
        if result.returncode != 0:
            sys.stderr.write(result.stderr)
            sys.exit(result.returncode)
        output = result.stdout
    sys.stdout.write(latex_document(output))


if __name__ == '__main__':
    main()
