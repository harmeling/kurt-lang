import contextlib
import io
import unittest

import kurt.kurt as kurt


class TestUnicodeSymbols(unittest.TestCase):
    # which characters are symbols (decided 2026-11-11): the Unicode symbol categories Sm, So, Sc, Sk and the letters of the
    # blocks of the mathematics, one character each, declared by the theory or the line; letters of other scripts are not

    def check(self, text, **options):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            result = kurt.check_text(text, name='symbols.kurt', session=kurt.Session(kurt.RunConfig(**options)) if options else None)
        return result, [line for line in err.getvalue().splitlines() if 'Warning:' in line]

    def test_a_mathematical_symbol_is_an_operator_when_declared(self):
        result, _ = self.check('infix ⋈ 50 50\nconst a, b\nuse a ⋈ b\nuse b ⋈ a\n')
        self.assertTrue(result.ok, result.error)

    def test_other_symbols_arrows_and_emoji_are_accepted(self):
        for symbol in ('⊗', '↪', '∮', '★', '€', '⤳'):
            result, _ = self.check(f'infix {symbol} 50 50\nconst a, b\nuse a {symbol} b\n')
            self.assertTrue(result.ok, f'{symbol}: {result.error}')

    def test_the_letters_of_the_mathematics_are_symbols(self):
        for symbol in ('𝒜', '𝔸', '𝐀', 'ℓ', 'ℂ'):
            result, _ = self.check(f'const {symbol}\nuse {symbol} = {symbol}\n')
            self.assertTrue(result.ok, f'{symbol}: {result.error}')

    def test_letters_of_other_scripts_and_invisible_characters_are_refused(self):
        for text in ('const а', 'const é', 'const ａ', 'const a​b', 'const x́', 'const 日'):
            result, _ = self.check(text + '\n')
            self.assertFalse(result.ok, text)
            self.assertIn('ScanError', result.error or '', text)

    def test_a_composed_and_a_decomposed_symbol_are_the_same_text(self):
        # `≠` is `=` and a combining slash, U+0338, written decomposed (NFC composes it)
        result, _ = self.check('load logic, equality\nconst a, b\nuse a ≠ b\na ≠ b\n')
        self.assertTrue(result.ok, result.error)

    def test_a_lookalike_of_an_ascii_character_is_warned_about(self):
        result, found = self.check('load number\nuse 1 − 1 = 0\n')
        self.assertTrue(result.ok, result.error)
        self.assertEqual(len(found), 1, found)
        self.assertIn('`−` is the minus sign U+2212, not the ASCII `-`', found[0])

    def test_strict_mode_refuses_a_lookalike(self):
        result, _ = self.check('load number\n1 − 1 = 0\n', strict=True)
        self.assertFalse(result.ok)
        self.assertIn('`−` is the minus sign U+2212', result.error or '')

    def test_a_symbol_with_a_shortcut_is_typed_with_its_name(self):
        self.assertEqual(kurt.REPLACEMENTS['\\bowtie'], '⋈')
        self.assertEqual(kurt.replace_latex_syntax('a \\bowtie b \\otimes c'), 'a ⋈ b ⊗ c')


if __name__ == '__main__':
    unittest.main()
