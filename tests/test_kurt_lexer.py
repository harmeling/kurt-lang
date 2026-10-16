import unittest
import kurt.kurt as kurt
from .examples import examples

class Test_Lexing(unittest.TestCase):
    def test_lexing(self):
        for i in range(len(examples)):
            (input_line, true_output, _) = examples[i]  # pick input, lexed
            try:
                result = kurt.scan_string(input_line, kurt.initial_kb)  # peekable token stream
                output = '[' + ', '.join([f'({t.label} "{t.value}")' for t in result]) + ']'
            except Exception as e:
                output = (str(e).split('\n'))[-1]    # this could be the desired result
            with self.subTest(msg=input_line, i=i):
                self.assertEqual(output, true_output)

    def test_symbols_of_sets_and_inverses(self):
        # refused by the scanner until 2026-10-12: `A ∖ B`, `∁A`, `u ⟂ v`, `A ∋ x`, `a⁻¹`
        # -- `⁻¹` is one symbol (as `∃!`), and each has a LaTeX shortcut
        for line, symbols in (('A ∖ B', ['A', '∖', 'B']), ('∁A', ['∁', 'A']), ('u ⟂ v', ['u', '⟂', 'v']),
                              ('A ∋ x', ['A', '∋', 'x']), ('a⁻¹ ∘ a', ['a', '⁻¹', '∘', 'a'])):
            with self.subTest(line=line):
                self.assertEqual([t.value for t in kurt.scan_string(line, kurt.initial_kb)][:-1], symbols)   # (without the end)
        for command, symbol in (('\\setminus', '∖'), ('\\complement', '∁'), ('\\perp', '⟂'), ('\\ni', '∋'), ('\\inv', '⁻¹')):
            self.assertEqual(kurt.replace_latex_syntax(f'a {command} b'), f'a {symbol} b')
        result = kurt.check_text('postfix ⁻¹ 85\nconst a\nparse a⁻¹\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('(⁻¹ a)', result.output)

    def test_names_with_primes_and_digits_and_the_symbols_of_relations(self):
        # until 2026-10-12 `a'` was `a` and `'`, `λ1` was `λ` and `1`, and `~` was refused
        for line, symbols in (("a' = a''", ["a'", '=', "a''"]), ('λ1 + ε2', ['λ1', '+', 'ε2']), ("ε' < ε", ["ε'", '<', 'ε']),
                              ("$x' = $x", ["$x'", '=', '$x']), ('a ~ b', ['a', '~', 'b']), ('a ∼ b ≈ c ≺ d ≼ e', ['a', '∼', 'b', '≈', 'c', '≺', 'd', '≼', 'e'])):
            with self.subTest(line=line):
                self.assertEqual([t.value for t in kurt.scan_string(line, kurt.initial_kb)][:-1], symbols)
        for command, symbol in (('\\sim', '∼'), ('\\approx', '≈'), ('\\prec', '≺'), ('\\preceq', '≼')):
            self.assertEqual(kurt.replace_latex_syntax(f'a {command} b'), f'a {symbol} b')

    def test_the_standard_latex_names(self):
        # missing until 2026-10-14: LaTeX's short forms and its names of the connectives, next to Kurt's own
        for command, symbol in (('\\le', '≤'), ('\\ge', '≥'), ('\\ne', '≠'), ('\\lnot', '¬'), ('\\land', '∧'),
                                ('\\wedge', '∧'), ('\\lor', '∨'), ('\\vee', '∨'), ('\\Rightarrow', '⇒'),
                                ('\\Leftrightarrow', '⇔'), ('\\bot', '⊥')):
            with self.subTest(command=command):
                self.assertEqual(kurt.replace_latex_syntax(f'a {command} b'), f'a {symbol} b')
        # only whole commands, the longer ones keep theirs
        self.assertEqual(kurt.replace_latex_syntax('\\leq \\geq \\neq \\neg \\leadsto \\bottom'), '≤ ≥ ≠ ¬ ⇝ ⊥')
        # what Kurt writes keeps Kurt's own names: `⇒` as `\\implies`, `≤` as `\\leq`
        self.assertEqual((kurt.TEX_UNICODE['⇒'], kurt.TEX_UNICODE['⇔'], kurt.TEX_UNICODE['≤'], kurt.TEX_UNICODE['≠']),
                         ('\\implies', '\\iff', '\\leq', '\\neq'))

if __name__ == '__main__':
    unittest.main()