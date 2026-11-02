import contextlib
import io
import unittest

import kurt.kurt as kurt


class TestForeignNotations(unittest.TestCase):
    # a notation of another language is declared by its first use (`a != b` is a claim about a new predicate `!=`):
    # a warning says the Kurt spelling, or the theory of Kurt that declares the symbol (decided 2026-11-02)
    def warnings(self, text):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            result = kurt.check_text(text, name='foreign.kurt')
        self.assertTrue(result.ok, result.error)
        return [line for line in err.getvalue().splitlines() if 'Warning:' in line]

    def test_the_kurt_spelling_of_a_foreign_notation_is_said(self):
        found = self.warnings('load logic\nconst a, b\nuse a != b\n')
        self.assertEqual(len(found), 1, found)
        self.assertIn('`!=` is not Kurt: write `≠`', found[0])

    def test_the_theory_that_declares_the_symbol_is_said(self):
        found = self.warnings('load logic\nconst a, b\nuse a ≤ b\n')
        self.assertEqual(len(found), 1, found)
        self.assertIn('`≤` is declared in number.kurt: `load number`?', found[0])

    def test_a_symbol_that_is_declared_is_not_warned_about(self):
        self.assertEqual(self.warnings('load logic, number\nconst a, b\nuse a ≤ b\n'), [])

    def test_strict_mode_refuses_the_symbol_and_says_the_spelling(self):
        result = kurt.check_text('load logic\nconst a, b\na != b\n', name='foreign.kurt', session=kurt.Session(kurt.RunConfig(strict=True)))
        self.assertFalse(result.ok)
        self.assertIn('`!=` is not Kurt: write `≠`', result.error or '')

    def test_the_symbol_for_a_subset_or_equal_is_in_set_kurt(self):
        result = kurt.check_text('load set\nconst A, B\nuse A ⊆ B\nuse B ⊇ A\n')
        self.assertTrue(result.ok, result.error)
        self.assertNotIn('const ⊆', result.output)

    def test_a_number_applied_to_something_is_hinted_when_the_step_fails(self):
        result = kurt.check_text('load number\nconst x\nreal x\nuse x = 2\n3 x = 6\n')
        self.assertFalse(result.ok)
        self.assertIn('`3 x` applies the number `3` to something', result.error or '')
        self.assertIn('for a product write `3 * x`', result.error or '')

    def test_a_keyword_in_capitals_is_hinted(self):
        for text, word in (('load propositional\nprop A\nuse A\nShow A\n', 'show'), ('Load propositional\nprop A\n', 'load')):
            result = kurt.check_text(text)
            self.assertFalse(result.ok)
            self.assertIn(f'did you mean `{word}`?', result.error or '')


if __name__ == '__main__':
    unittest.main()
