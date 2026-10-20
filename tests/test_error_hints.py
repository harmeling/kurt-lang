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
        error = self.error('load propositional\nconst odd_sum\n')
        self.assertIn('`odd_sum` is not one name', error)
        self.assertIn('`odd`, `_`, `sum`', error)
        self.assertTrue(kurt.check_text('load propositional\nconst oddsum, odd2\n').ok)
        self.assertIn('e.g. `oddsum`', error)
        self.assertIn('`a_b` is not one name', self.error('load propositional\nflat a_b\n'))   # (the other declarations)
        self.assertIn('wrong arguments', self.error('load propositional\nconst a b\n'))   # (not glued)

    def test_def_by_a_tuple_of_variables(self):
        # `child($x, $y)` is `child` of the pair (since 2026-10-12, before: an error without `arity
        # child 2`): a tuple of distinct variables is a left-hand side, a tuple with a constant isn't
        result = kurt.check_text('load equality\nconst a, b\nprop child 0\ndef child($x, $y) ⇔ $x = $y\nuse a = b\nchild(a, b)\n')
        self.assertTrue(result.ok, result.error)
        error = self.error('load equality\nconst a\nprop child 0\ndef child($x, a) ⇔ $x = a\n')
        self.assertIn('applied to variables on the left-hand side', error)
        error = self.error('load equality\nprop child 0\ndef child($x, $x) ⇔ $x = $x\n')
        self.assertIn('distinct variables', error)

    def test_def_of_a_declared_constant(self):
        error = self.error('load equality\nconst c\ndef c = 1\n')
        self.assertIn('`c` is declared already', error)

    def test_a_relation_as_a_parameter(self):
        # `$R(x, x)` is a term: the error says how to write a relation as a parameter (2026-10-12)
        error = self.error('load logic, set\nprop reflexive 0\ndef reflexive($R, $A) ⇔ ∀ x ∈ $A ($R(x, x))\n')
        self.assertIn('`var R`, `prop R 0`', error)
        result = kurt.check_text('load logic, set\nconst A, lt\nprop lt 0\nprop reflexive 0\nvar R\nprop R 0\n'
                                 'def reflexive((R), $A) ⇔ ∀ x ∈ $A (R(x, x))\nuse ∀ x ∈ A (lt(x, x))\nreflexive(lt, A)\n')
        self.assertTrue(result.ok, result.error)


if __name__ == '__main__':
    unittest.main()
