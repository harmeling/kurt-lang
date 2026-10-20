import os
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# `kurt --latex FILE` / `--markdown` (`export_document`, before 2026-10-13 the text-based
# scripts/kurt2latex.py): each line in mathematical notation, by the `tex` declarations of the
# theories (`tex sum \sum_{$1=$2}^{$3} $4`) and defaults, with its reason, and the certificates


def export(text: str, fmt: str) -> str:
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'proof.kurt')
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(text)
        return kurt.export_document(path, fmt, kurt.RunConfig())


class TestExportDocument(unittest.TestCase):
    def test_the_notation_of_the_theories(self):
        doc = export('load sequences\nconst x, y\nuse x ≠ y\nuse x ∈ Nat\nuse (sum i (0, 3) i) = 6\n'
                     'use converges n 0 (1 / n)\nuse tends v 2 7 (3 * v + 1)\n', 'markdown')
        self.assertIn(r'x \neq y', doc)                              # `¬(x = y)`, how `≠` is read
        self.assertIn(r'x \in \mathbb{N}', doc)                      # natural.kurt: `tex Nat \mathbb{N}`
        self.assertIn(r'\sum_{{i}={0}}^{{3}}', doc)                  # analysis.kurt: the places of `sum`
        self.assertIn(r'\frac{{1}}{{n}}', doc)
        self.assertIn(r'\underset{{n} \to \infty}{\longrightarrow}', doc)
        self.assertIn('| 3 |', doc)                                  # Kurt's line numbers, in a table

    def test_variables_and_a_declaration_of_ones_own(self):
        doc = export('load equality\nconst x, f\ntex f \\varphi($1)\nuse f($y) = $y\nuse $x = x\n', 'markdown')
        self.assertIn(r'{\varphi({y})} = y', doc)                    # `$y` as on paper: `y`
        self.assertIn(r'\mathsf{x} = x', doc)                        # but not where a constant `x` is too

    def test_latex_document_with_certificates(self):
        doc = export('load propositional\nprop A, B\nuse A implies B\nuse A\nB\n', 'latex')
        self.assertTrue(doc.startswith(r'\documentclass') and doc.rstrip().endswith(r'\end{document}'))
        self.assertIn(r'A \Rightarrow B', doc)
        self.assertIn(r'\section*{Certificates}', doc)
        self.assertIn('Proof checked', doc)
        self.assertFalse([c for c in doc if ord(c) > 127])              # all symbols as LaTeX (pdflatex)

    def test_tex_needs_a_symbol_and_latex(self):
        result = kurt.check_text('tex\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('no tex declarations', result.output)


class TestTuples(unittest.TestCase):
    def test_a_tuple_argument_in_the_brackets_of_the_call(self):
        # `R(x, x)` was written `R\left(\left(x, x\right)\right)` until 2026-10-14
        doc = export('load set\nconst R, x\nuse R(x, x)\nuse (x, x) = (x, x)\n', 'markdown')
        self.assertIn(r'R\left(x, x\right)$', doc)
        self.assertIn(r'\left(x, x\right) = \left(x, x\right)', doc)


class TestChains(unittest.TestCase):
    def test_a_chain_without_its_first_term_on_the_continuation_lines(self):
        # until 2026-10-14 each continuation line repeated the left side (`e < g`, `e < h`)
        doc = export('load numbers\nconst e, f, g, h\nuse e = f\nuse f < g\nuse g = h\ne = f\n  < g\n  = h\ncalc on\n- 1 < 0\n', 'markdown')
        self.assertIn('| 6 | $e = f$ |', doc)
        self.assertIn('| 7 | $< g$ |', doc)
        self.assertIn('| 8 | $= h$ |', doc)
        self.assertNotIn('| 10 | $< 0$', doc)                         # a line starting with `-` isn't a continuation

    def test_a_proof_that_does_not_check_keeps_its_notation(self):
        # until 2026-10-14 the document of a failed check was written without the theories' notation (`e\left(=, f\right)`)
        doc = export('load numbers\nconst e, f\nuse e = f\nf < e\n', 'markdown')
        self.assertIn('not checked', doc)
        self.assertIn('$\\textbf{use} \\; e = f$', doc)


def run_cli(text: str, *options: str) -> tuple[subprocess.CompletedProcess, str]:
    # `kurt OPTIONS proof.kurt` in a directory of its own: the result, and the directory's files afterwards
    env = dict(os.environ)
    env['PYTHONPATH'] = str(PROJECT_ROOT / 'src') + os.pathsep + env.get('PYTHONPATH', '')
    with tempfile.TemporaryDirectory() as tmp:
        with open(os.path.join(tmp, 'proof.kurt'), 'w', encoding='utf-8') as fh:
            fh.write(text)
        result = subprocess.run([sys.executable, '-m', 'kurt.kurt', '--no-kurtc', *options, 'proof.kurt'],
                                cwd=tmp, env=env, capture_output=True, text=True, timeout=60)
        return result, ' '.join(sorted(os.listdir(tmp)))


class TestOutputOption(unittest.TestCase):
    # `-o FILE` / `-o -` (2026-10-14; before, the document always went next to the file)
    def test_to_standard_output(self):
        result, files = run_cli('prop A\nuse A\nA\n', '--markdown', '-o', '-')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(result.stdout.startswith('# proof.kurt'), result.stdout)   # only the document
        self.assertEqual(files, 'proof.kurt')                                     # nothing written

    def test_a_failed_check_writes_nothing_to_standard_output(self):
        result, _ = run_cli('prop A, B\nuse A\nB\n', '--latex', '-o', '-')
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, '')
        self.assertIn('ProofError', result.stderr)

    def test_to_a_file(self):
        result, files = run_cli('prop A\nuse A\nA\n', '--latex', '-o', 'doc.tex')
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(files, 'doc.tex proof.kurt')
        self.assertIn('wrote doc.tex', result.stdout)

    def test_refused(self):
        for options, message in ((('--latex', '--markdown', '-o', '-'), 'one of'), (('-o', 'x.md'), 'needs'),
                                 (('--latex', '-o', 'proof.kurt'), 'the file being checked')):
            with self.subTest(options=options):
                result, files = run_cli('prop A\nuse A\nA\n', *options)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(message, result.stderr)
                self.assertEqual(files, 'proof.kurt')


if __name__ == '__main__':
    unittest.main()
