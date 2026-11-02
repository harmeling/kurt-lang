import copy
import unittest

import kurt.kurt as kurt

# an operator written with its holes, `_+_`, `-_`, `_!` (todo 73, the first step): the operator as a term, applied it is the
# operator between its arguments (proofs/debug/operators-with-holes.kurt has the proofs)


NUMBER_KB = copy.deepcopy(kurt.initial_kb)
kurt.load_file('number.kurt', NUMBER_KB)


def scanned(text: str) -> list[tuple]:
    return [(t.value, t.shaped) for t in kurt.scan_string(text, NUMBER_KB) if t.label != 'END']


def ok(text: str) -> bool:
    return kurt.Session().check_text('load number\nconst a, b\n' + text).ok


class TestShapedOperators(unittest.TestCase):
    def test_the_shapes(self):
        self.assertEqual(scanned('_+_ -_ _-_'), [('+', 'infix'), ('-', 'prefix'), ('-', 'infix')])
        self.assertEqual(scanned('_∧_'), [('and', 'infix')])
        self.assertEqual(scanned('_implies_'), [('implies', 'infix')])

    def test_other_underscores_are_left_alone(self):
        # the shapes of `arity`, a name that is no operator
        self.assertEqual([shaped for _, shaped in scanned('arity g (_, _, _)') if shaped], [])
        self.assertEqual([shaped for _, shaped in scanned('(_,_)') if shaped], [])

    def test_applied_it_is_the_operator_between_the_arguments(self):
        self.assertTrue(ok('show a + b = _+_(a, b)\nproof\n    a + b = a + b\n'))
        self.assertTrue(ok('show a + b = _+_ a b\nproof\n    a + b = a + b\n'))
        self.assertTrue(ok('show - a = -_(a)\nproof\n    - a = - a\n'))

    def test_the_wrong_shape_is_an_error(self):
        result = kurt.Session().check_text('load number\nconst a\nshow _not_(a, a)\n')
        self.assertIn('is the infix operator `not` with its holes, but `not` is a prefix operator (write `not_`)', ''.join(str(e) for e in result.errors))

    def test_the_wrong_number_of_arguments(self):
        result = kurt.Session().check_text('load number\nconst a, b\nshow a + b = _+_(a)\n')
        self.assertIn('takes 2 arguments', ''.join(str(e) for e in result.errors))

    def test_an_operator_that_is_not_declared_is_an_error(self):
        # (before 2026-11-01 `_+_` without `number` was a new constant of that name)
        result = kurt.Session().check_text('load group\nconst R\nuse group(R, _+_, 0, -_)\n')
        self.assertIn('`_+_` is `+` with its holes, but `+` is no operator here', ''.join(str(e) for e in result.errors))


if __name__ == '__main__':
    unittest.main()
