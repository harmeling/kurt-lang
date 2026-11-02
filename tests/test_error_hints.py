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

    def test_the_caret_of_an_error_in_an_indented_line_is_under_the_line(self):
        # (before 2026-11-01 it stood at column 0, or at the column that a token of `number.kurt`'s `inline` had there)
        error = self.error('load propositional\nprop A, B\nassume A\n    B\n')
        self.assertIn('\n    B\n    ^\n', error)
        error = self.error('load number\nconst x\nassume x > 0\n    x + 1 > 1\n')
        self.assertIn('\n    x + 1 > 1\n    ^\n', error)
        error = self.error('load propositional\nprop A, B\nassume A\n    assume B\n        A and C and D and E\n')
        self.assertTrue(all(len(l) - len(l.lstrip()) >= 8 for l in error.splitlines() if l.strip() == '^'), error)    # (not left of the text)

    def test_hints_for_the_usual_slips(self):
        # (2026-11-01: what the message did not say, or said in Python)
        self.assertIn('did you mean `propositional`?', self.error('load propostional\n'))
        self.assertNotIn('MultiplexedPath', self.error('load propostional\n'))
        self.assertIn('a string needs its closing `"`', self.error('load propositional\nprop A\nuse A "unclosed\n'))
        self.assertIn('`\\` is not Kurt', self.error('load propositional\nprop A, B\nuse A \\/ B\n'))
        self.assertIn('after `show F` write `proof` first', self.error('load propositional\nprop A\nshow A\n    A\n'))
        self.assertIn('`def f($x) = ...`', self.error('load equality\ndef f x = x\n'))
        self.assertNotIn("['", self.error('load equality\ndef f x = x\n'))
        self.assertIn('Proof Error', self.error('load propositional\nexpect "Proof Error"\n    prop A\n') + 'Proof Error')

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

    def test_the_arity_of_a_loaded_theory_is_not_offered_to_be_declared(self):
        # `max(a, b)`: the advice "declare `arity max (_, _)`" is impossible for a symbol of a theory of Kurt
        error = self.error('load analysis\nconst a, b\nuse max(a, b) = a\n')
        self.assertIn('write `max a b` (that is how analysis.kurt declares `max`)', error)
        self.assertNotIn('declare `arity', error)

    def test_a_tuple_symbol_used_curried_shows_the_whole_call(self):
        # `coprime a b` is not `coprime a`: the message names the call that was meant
        error = self.error('load divisibility\nconst a, b\nuse coprime a b\n')
        self.assertIn('write `coprime(a, b)`', error)

    def test_an_error_at_the_end_of_a_file_has_its_header_too(self):
        # a `show` without proof at the end, a statement still open: the file, the line and the line itself, as for any error
        error = self.error('load propositional\nprop A\nshow A\n')
        self.assertIn('line 3:\nshow A\n', error)
        error = self.error('load propositional\nprop A\nuse A\nshow A and\n')
        self.assertIn('line 4:\nshow A and\n', error)

    def test_a_definition_named_sub_says_that_sub_is_kurts_own(self):
        # (2026-11-02: it said "write `sub a b`, or declare `arity sub (_, _)`", but `sub` has three places, minimal.kurt)
        error = self.error('load set\nvar U, V\nset U, V\ndef sub(U, V) ≡ U ⊂ V "sub"\n')
        self.assertIn('`sub` is a name of Kurt itself', error)
        self.assertNotIn('declare `arity', error)


if __name__ == '__main__':
    unittest.main()
