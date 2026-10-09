import unittest

import kurt


class TestSyntaxSoundness(unittest.TestCase):
    def assert_rejected(self, source: str, text: str) -> None:
        result = kurt.check_text(source, name='syntax-soundness.kurt')
        self.assertFalse(result.ok, result.output)
        self.assertIsNotNone(result.error)
        self.assertIn(text, result.error or '')

    def test_flat_prefix_overload_cannot_erase_prefix(self):
        # Before the guard, flattening normalized `f (A f B)` to `A f B`, so these two
        # satisfiable axioms let the prover conclude `false`.
        contradiction = '''\
load prop
prefix f 90
infix f 50 50
flat f
bool f 0 1 2
bool A, B
use not f (A f B)
use A f B
false
'''
        self.assert_rejected(contradiction, 'can not be `flat`')
        self.assert_rejected('infix f 50 50\nflat f\nprefix f 90\n', 'can not also be prefix')

    def test_symmetric_binder_cannot_swap_bound_variable_and_body(self):
        # `x q y` and `y q x` are different binders. Symmetric normalization used to sort
        # both into the same tree, again accepting `false` from consistent assumptions.
        contradiction = '''\
load prop
infix q 20 20
bindop q
sym q
var x, y
bool x, y
use not (x q y)
use y q x
false
'''
        self.assert_rejected(contradiction, 'can not be `sym`')
        self.assert_rejected('infix q 20 20\nsym q\nbindop q\n', 'can not be a binding operator')

    def test_binder_rejects_other_incompatible_meanings(self):
        cases = (
            ('infix q 20 20\nbindop q\nprefix q 90\n', 'can not also be prefix'),
            ('infix q 20 20\nbindop q\nchain q\n', 'can not be in a chain'),
            ('infix q 20 20\nchain q\nbindop q\n', 'can not be a binding operator'),
            ('infix q 20 20\nbuiltin q add\nbindop q\n', 'can not also be a binding operator'),
            ('infix q 20 20\nbindop q\nbuiltin q add\n', 'can not also be a calculator operation'),
        )
        for source, message in cases:
            with self.subTest(source=source):
                self.assert_rejected(source, message)

    def test_semantic_properties_belong_to_concrete_operators(self):
        for declaration in ('flat f', 'sym f', 'chain f'):
            with self.subTest(declaration=declaration):
                self.assert_rejected(f'var f\ninfix f 20 20\n{declaration}\n', 'variable operator')
        self.assert_rejected('var f\narity f 2\nbindop f\n', 'fixed binding scope')
        self.assert_rejected('infix f 20 20\nsym f\nvar f\n', 'already used as a constant')

    def test_bool_positions_fit_declared_arity(self):
        self.assert_rejected('prefix f 90\nbool f 0 2\n', 'between 0 and its arity 1')
        self.assert_rejected('arity f 1\nbool f 0 2\n', 'between 0 and its arity 1')
        self.assert_rejected('bool f 0 2\narity f 1\n', 'more than 1 arg')
        self.assert_rejected('arity f 2\nbool f 0 1 1\n', 'must be different')
        self.assert_rejected('bool f 0 1\narity f 2\nbindop f\n', 'first position')

    def test_calculator_result_type_is_fixed(self):
        self.assert_rejected('builtin f add\nbool f 0\n', 'non-boolean result')
        self.assert_rejected('bool f 0\nbuiltin f add\n', 'non-boolean result')
        result = kurt.check_text('builtin r eq\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('const r', result.output)
        self.assertIn('bool r 0', result.output)

    def test_declaration_categories_are_order_independent(self):
        for fixity in ('prefix f 90', 'infix f 50 50', 'postfix f 90'):
            with self.subTest(fixity=fixity):
                self.assert_rejected(f'arity f 2\n{fixity}\n', 'explicit arity')
        for prior in ('arity left 1', 'bool left', 'builtin left add'):
            with self.subTest(prior=prior):
                self.assert_rejected(f'{prior}\nbrackets left right\n', 'already has an')
        self.assert_rejected('builtin f add\nvar f\n', 'already used as a constant')
        self.assert_rejected('var f\nbuiltin f add\n', 'fixed calculator meaning')
        self.assert_rejected('builtin f add\nalias f true\n', 'already a constant')

    def test_bool_on_left_bracket_types_the_bracket_expression(self):
        result = kurt.check_text('brackets [ ]\nbool [ 0 1\nuse [true]\nbool\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('bool [ 0 1', result.output)
        self.assertNotIn('$$$', result.output)
        self.assert_rejected('brackets [ ]\nbool ]\n', 'left bracket')
        self.assert_rejected('brackets [ ]\nbuiltin ] matrix\n', 'left bracket')
        calc = kurt.check_text('brackets [ ]\nbuiltin [ matrix\n')
        self.assertTrue(calc.ok, calc.error)
        self.assertIn('builtin [ matrix', calc.output)
        self.assertNotIn('$$$', calc.output)

    def test_failed_declaration_batches_do_not_change_shell_state(self):
        cases = (
            ('prefix f 10, f 20', 'prefix', 'prefix f '),
            ('const a, a', 'const', 'const a '),
            ('bool A, A', 'bool', 'bool A '),
            ('arity f 1, f 2', 'arity', 'arity f '),
        )
        for declaration, query, leaked in cases:
            with self.subTest(declaration=declaration):
                shell = kurt.Shell()
                shell.start_text('')
                error = shell.feed(declaration)
                self.assertIn('Error:', error)
                self.assertNotIn(leaked, shell.feed(query))


if __name__ == '__main__':
    unittest.main()
