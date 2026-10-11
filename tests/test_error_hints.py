import unittest

import kurt.kurt as kurt

# error messages that say what to do -- the cases students of exercises/ ran into (2026-10-11)


class TestErrorHints(unittest.TestCase):
    def error(self, text: str) -> str:
        result = kurt.check_text(text)
        self.assertFalse(result.ok)
        return result.error or ''

    def test_a_bound_variable_named_like_a_constant(self):
        self.assertIn('give the bound variable another name', self.error('load logic\nconst x\n∃ x (x = x)\n'))
        self.assertIn('give the bound variable a new name', self.error('load set\nconst A\nlet x\n    ∃ x ∈ A (x = x)\n'))

    def test_a_name_with_an_underscore(self):
        error = self.error('load prop\nconst odd_sum\n')
        self.assertIn('`odd_sum` is not one name', error)
        self.assertIn('`odd`, `_`, `sum`', error)
        self.assertTrue(kurt.check_text('load prop\nconst oddsum, odd2\n').ok)
        self.assertIn('e.g. `oddsum`', error)
        self.assertIn('`a_b` is not one name', self.error('load prop\nflat a_b\n'))   # (the other declarations)
        self.assertIn('wrong number of arguments', self.error('load prop\nconst a b\n'))   # (not glued)

    def test_def_without_the_arity(self):
        error = self.error('load equality\nbool child 0\ndef child($x, $y) ⇔ $x = $y\n')
        self.assertIn('without `arity child 2` before the `def`', error)

    def test_def_of_a_declared_constant(self):
        error = self.error('load equality\nconst c\ndef c = 1\n')
        self.assertIn('`c` is declared already', error)


if __name__ == '__main__':
    unittest.main()
