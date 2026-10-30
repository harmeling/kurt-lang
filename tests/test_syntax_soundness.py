import tempfile
import unittest
from pathlib import Path

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
load propositional
prefix f 90
infix f 50 50
flat f
prop f 0 1 2
prop A, B
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
load propositional
infix q 20 20
binder q
sym q
var x, y
prop x, y
use not (x q y)
use y q x
false
'''
        self.assert_rejected(contradiction, 'can not be `sym`')
        self.assert_rejected('infix q 20 20\nsym q\nbinder q\n', 'can not be a binding operator')

    def test_binder_rejects_other_incompatible_meanings(self):
        cases = (
            ('infix q 20 20\nbinder q\nprefix q 90\n', 'can not also be prefix'),
            ('infix q 20 20\nbinder q\nchain q\n', 'can not be in a chain'),
            ('infix q 20 20\nchain q\nbinder q\n', 'can not be a binding operator'),
            ('infix q 20 20\nbuiltin q add\nbinder q\n', 'can not also be a binding operator'),
            ('infix q 20 20\nbinder q\nbuiltin q add\n', 'can not also be a calculator operation'),
        )
        for source, message in cases:
            with self.subTest(source=source):
                self.assert_rejected(source, message)

    def test_semantic_properties_belong_to_concrete_operators(self):
        for declaration in ('flat f', 'sym f', 'chain f'):
            with self.subTest(declaration=declaration):
                self.assert_rejected(f'var f\ninfix f 20 20\n{declaration}\n', 'variable operator')
        self.assert_rejected('var f\narity f 2\nbinder f\n', 'fixed binding scope')
        self.assert_rejected('infix f 20 20\nsym f\nvar f\n', 'already used as a constant')

    def test_bool_positions_fit_declared_arity(self):
        self.assert_rejected('prefix f 90\nprop f 0 2\n', 'between 0 and its arity 1')
        self.assert_rejected('arity f 1\nprop f 0 2\n', 'between 0 and its arity 1')
        self.assert_rejected('prop f 0 2\narity f 1\n', 'more than 1 arg')
        self.assert_rejected('arity f 2\nprop f 0 1 1\n', 'must be different')
        self.assert_rejected('prop f 0 1\narity f 2\nbinder f\n', 'first position')

    def test_calculator_result_type_is_fixed(self):
        self.assert_rejected('builtin f add\nprop f 0\n', 'a term as its result')
        self.assert_rejected('prop f 0\nbuiltin f add\n', 'a term as its result')
        result = kurt.check_text('builtin r eq\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('const r', result.output)
        self.assertIn('prop r 0', result.output)

    def test_declaration_categories_are_order_independent(self):
        for fixity in ('prefix f 90', 'infix f 50 50', 'postfix f 90'):
            with self.subTest(fixity=fixity):
                self.assert_rejected(f'arity f 2\n{fixity}\n', 'explicit arity')
        for prior in ('arity left 1', 'prop left', 'builtin left add'):
            with self.subTest(prior=prior):
                self.assert_rejected(f'{prior}\nbrackets left right\n', 'already has an')
        self.assert_rejected('builtin f add\nvar f\n', 'already used as a constant')
        self.assert_rejected('var f\nbuiltin f add\n', 'fixed calculator meaning')
        self.assert_rejected('builtin f add\nalias f true\n', 'already a constant')

    def test_bool_on_left_bracket_types_the_bracket_expression(self):
        result = kurt.check_text('brackets [ ]\nprop [ 0 1\nuse [true]\nprop\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('prop [ 0 1', result.output)
        self.assertNotIn('$$$', result.output)
        self.assert_rejected('brackets [ ]\nprop ]\n', 'left bracket')
        calc = kurt.check_text('brackets [ ]\nbuiltin [ ] matrixbrackets\n')
        self.assertTrue(calc.ok, calc.error)
        self.assertIn('builtin [ ] matrixbrackets', calc.output)
        self.assertNotIn('$$$', calc.output)

    def test_a_role_of_brackets_needs_a_declared_bracket_pair(self):
        # until 2026-10-12 `builtin [ matrix` took any symbol, also one never declared a bracket
        # (then nothing happened), and a bracket pair took any role (`builtin [ add`)
        self.assert_rejected('builtin [ ] matrixbrackets\n', 'not a declared bracket pair')
        self.assert_rejected('brackets ⟨ ⟩\nbuiltin [ ] matrixbrackets\n', 'not a declared bracket pair')
        self.assert_rejected('brackets [ ]\nbrackets ⟨ ⟩\nbuiltin [ ⟩ matrixbrackets\n', 'not a declared bracket pair')
        self.assert_rejected('brackets [ ]\nbuiltin ] [ matrixbrackets\n', 'not a declared bracket pair')
        self.assert_rejected('brackets [ ]\nbuiltin [ matrixbrackets\n', 'give both brackets')
        self.assert_rejected('brackets [ ]\nbuiltin [ add\n', 'only takes a role of a bracket pair')
        self.assert_rejected('brackets [ ]\nbuiltin ] add\n', 'only takes a role of a bracket pair')
        self.assert_rejected('brackets [ ]\nbuiltin [ ] add\n', 'not a role of a bracket pair')
        shown = kurt.check_text('brackets [ ]\nbuiltin [ ] matrixbrackets\nbuiltin\n')
        self.assertTrue(shown.ok, shown.error)
        self.assertIn('builtin [ ] matrixbrackets', shown.output)

    def test_the_roles_of_sets_only_in_a_theory_of_kurt(self):
        # `builtin { } setbrackets` changes which terms `{ }` makes (since 2026-10-12): a role of
        # the engine, not for a file of one's own; `setbuilder` needs an infix binder and the
        # brackets of sets
        self.assert_rejected('brackets { }\nbuiltin { } setbrackets\n', 'only be given by a theory that comes with Kurt')
        self.assert_rejected('infix | 10 10\nbinder |\nbuiltin | setbuilder\n', 'only be given by a theory that comes with Kurt')
        for source, text in (('infix | 10 10\nbinder |\nbuiltin | setbuilder\n', 'brackets of sets first'),
                             ('brackets { }\nbuiltin { } setbrackets\nconst |\nbuiltin | setbuilder\n', 'infix binder'),
                             ('brackets { }\nbuiltin { } setbrackets\nuse {} = {}\n', 'emptyset')):
            with self.subTest(source=source), tempfile.TemporaryDirectory() as folder:
                Path(folder, 'roles.kurt').write_text(source, encoding='utf-8')     # trusted: found via `-p`
                result = kurt.check_text('load roles\n', session=kurt.new_session(kurt.RunConfig(paths=(folder,))))
                self.assertFalse(result.ok, result.output)
                self.assertIn(text, result.error or '')

    def test_failed_declaration_batches_do_not_change_shell_state(self):
        cases = (
            ('prefix f 10, f 20', 'prefix', 'prefix f '),
            ('const a, a', 'const', 'const a '),
            ('prop A, A', 'prop', 'prop A '),
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
