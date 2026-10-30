import os
import tempfile
import unittest

import kurt.kurt as kurt

# `binder forall 17`: the binding power of the body of a binder (plan step 9, dev/todo.md) -- the operators that bind
# tighter than it are inside the body, `Q x x < 5 and R x` is `(Q x (x < 5)) and R x`; without a power the body is one tight
# argument, as before: `Q x x < 5` is `(Q x x) < 5`

HEAD = '''load propositional, equality
infix < 20 20
infix + 60 60
const Q, P, R
arity Q 2
prop P 1, R 1
'''


def parsed(declaration: str, *lines: str) -> list[str]:
    result = kurt.Session().check_text(HEAD + declaration + '\n' + '\n'.join(f'parse {line}' for line in lines) + '\n')
    assert result.ok, result.error
    return [l for l in result.output.splitlines() if l.startswith('(')]


class TestBinderPower(unittest.TestCase):
    def test_without_a_power_the_body_is_one_tight_argument(self):
        self.assertEqual(parsed('binder Q', 'Q x x < 5 and R x'), ['(and (< (Q x x) 5) (R x))'])

    def test_with_a_power_the_tighter_operators_are_in_the_body(self):
        self.assertEqual(parsed('binder Q 17', 'Q x x < 5 and R x', 'Q x x + 1 < 5'),
                         ['(and (Q x (< x 5)) (R x))', '(Q x (< (+ x 1) 5))'])

    def test_an_application_is_the_body(self):
        self.assertEqual(parsed('binder Q 17', 'Q x P x and R x'), ['(and (Q x (P x)) (R x))'])

    def test_a_power_for_one_of_a_list(self):
        self.assertEqual(parsed('const S\narity S 2\nbinder Q 17, S', 'S x x < 5', 'Q x x < 5'), ['(< (S x x) 5)', '(Q x (< x 5))'])

    def test_the_power_goes_with_the_declaration_into_a_loader(self):
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, 'quant.kurt'), 'w', encoding='utf-8') as f:
                f.write(HEAD + 'binder Q 17\nuse Q x (x < 5) "q"\n')
            session = kurt.Session(kurt.RunConfig(paths=(d,)))
            result = session.check_text('load quant\nparse Q x x < 5 and R x\n')
            self.assertTrue(result.ok, result.error)
            self.assertIn('(and (Q x (< x 5)) (R x))', result.output)

    def test_a_power_is_a_number_below_the_application(self):
        for power in (0, 90, 100):
            result = kurt.Session().check_text(HEAD + f'binder Q {power}\n')
            self.assertEqual(result.error_kind, 'EvalError', power)

    def test_an_infix_binder_has_no_power(self):
        result = kurt.Session().check_text(HEAD + 'infix | 10 10\nbinder | 17\n')
        self.assertEqual(result.error_kind, 'EvalError')


class TestNested(unittest.TestCase):
    # `nested forall, exists`: which binders take a list of variables
    def test_a_nested_binder_repeats_for_a_list(self):
        self.assertEqual(parsed('binder Q 17\nnested Q', 'Q x, y x < y'), ['(Q x (Q y (< x y)))'])

    def test_a_binder_that_is_not_nested_refuses_a_list(self):
        result = kurt.Session().check_text(HEAD + 'binder Q\nparse Q x, y x < y\n')
        self.assertFalse(result.ok)

    def test_only_a_binder_can_be_nested(self):
        result = kurt.Session().check_text(HEAD + 'nested P\n')
        self.assertEqual(result.error_kind, 'EvalError')

    def test_nested_goes_with_the_binder_into_a_loader(self):
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, 'quant.kurt'), 'w', encoding='utf-8') as f:
                f.write(HEAD + 'binder Q 17\nnested Q\nuse Q x (x < 5) "q"\n')
            result = kurt.Session(kurt.RunConfig(paths=(d,))).check_text('load quant\nparse Q x, y x < y\n')
            self.assertTrue(result.ok, result.error)
            self.assertIn('(Q x (Q y (< x y)))', result.output)

    def test_the_quantifiers_are_nested(self):
        result = kurt.Session().check_text('load logic, number\nparse forall x > 0, y > 0 (x < y)\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('(forall (< 0 x) (forall (< 0 y) (< x y)))', result.output)
