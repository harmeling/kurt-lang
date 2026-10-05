import importlib.util
import os
import unittest

# `scripts/kurt2latex.py` turns Kurt's output into a LaTeX document (formatting only, not part
# of Kurt itself)
_path = os.path.join(os.path.dirname(__file__), '..', 'scripts', 'kurt2latex.py')
_spec = importlib.util.spec_from_file_location('kurt2latex', _path)
kurt2latex = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(kurt2latex)


class TestKurt2Latex(unittest.TestCase):
    def test_rows_symbols_and_indentation(self):
        output = ('show A implies B                          ; 3 claim\n'
                  'proof\n'
                  '    assume A                              ; 5 open block with assumption\n'
                  'Proof checked\n')
        doc = kurt2latex.latex_document(output)
        self.assertIn(r'\text{To show: } A \Rightarrow B$ & 3 claim \\', doc)
        self.assertIn(r'$\quad \text{Assume that } A$', doc)
        self.assertIn('% Proof checked', doc)
        self.assertTrue(doc.startswith(r'\documentclass') and doc.rstrip().endswith(r'\end{document}'))

    def test_symbols_names_and_comments(self):
        output = ('($b ∘ (inv $b)) = e                      ; (ii) with α\n'
                  '                                          ; 30a by G4(23)\n'
                  '⟨ ($x , $y) ⟩ ∈ K                        ; 31 by S-map(a_b, 30)\n')
        doc = kurt2latex.latex_document(output)
        self.assertIn(r'$ (b \circ (\mathrm{inv} b)) = e$ & (ii) with $\alpha$ --- 30a by G4(23) \\', doc)   # one row
        self.assertIn(r'\langle  (x , y) \rangle  \in K', doc)
        self.assertIn(r'S-map(a\_b, 30)', doc)
        self.assertFalse([c for c in doc if ord(c) > 127])                                    # all symbols as LaTeX


if __name__ == '__main__':
    unittest.main()
