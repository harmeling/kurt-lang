import os
import tempfile
import unittest

import kurt
import kurt.kurt as core


class TestOptionalSorts(unittest.TestCase):
    def test_sparse_signatures_and_mixed_operator(self):
        result = kurt.check_text(
            'sort nat, vec\n'
            'nat n\n'
            'vec v, scale 0 2\n'
            'nat scale 1\n'
            'arity scale 2\n'
            'bool P\n'
            'arity P 1\n'
            'use P (scale n v)\n'
        )
        self.assertTrue(result.ok, result.error)

        wrong = kurt.check_text(
            'sort nat, vec\n'
            'nat n\n'
            'vec v, scale 0 2\n'
            'nat scale 1\n'
            'arity scale 2\n'
            'bool P\n'
            'arity P 1\n'
            'use P (scale v n)\n'
        )
        self.assertFalse(wrong.ok)
        self.assertIn('must have sort `nat`', wrong.error or '')

    def test_sort_property_does_not_choose_const_or_var(self):
        variable = kurt.check_text('sort nat\nnat a\nvar a\n')
        constant = kurt.check_text('sort nat\nnat a\nconst a\n')
        self.assertTrue(variable.ok, variable.error)
        self.assertTrue(constant.ok, constant.error)

    def test_bool_is_builtin_and_sort_names_are_reserved(self):
        redeclared = kurt.check_text('sort bool\n')
        self.assertFalse(redeclared.ok)
        self.assertIn('built-in judgment sort', redeclared.error or '')

        used = kurt.check_text('sort nat\nbool P\narity P 1\nuse P nat\n')
        self.assertFalse(used.ok)
        self.assertIn('cannot be used as a term symbol', used.error or '')

        declared = kurt.check_text('sort nat\nconst nat\n')
        self.assertFalse(declared.ok)
        self.assertIn('cannot also be a constant', declared.error or '')

    def test_conflicting_position_sorts_are_rejected(self):
        result = kurt.check_text('sort nat\nnat a\nbool a\n')
        self.assertFalse(result.ok)
        self.assertIn('already has sort nat', result.error or '')

    def test_sort_listing_has_origins(self):
        result = kurt.check_text('sort nat\nnat a\nsort\nnat\n', name='typed.kurt')
        self.assertTrue(result.ok, result.error)
        self.assertIn('sort bool', result.output)
        self.assertIn('builtin', result.output)
        self.assertIn('sort nat', result.output)
        self.assertIn('typed.kurt:1', result.output)
        self.assertIn('nat a 0', result.output)
        self.assertIn('typed.kurt:2', result.output)

    def test_sort_signatures_survive_load(self):
        with tempfile.TemporaryDirectory() as tmp:
            helper = os.path.join(tmp, 'typed.kurt')
            with open(helper, 'w') as stream:
                stream.write('sort term\nterm c\nbool P\narity P 1\nuse P c "typed"\n')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            result = session.check_text('load typed\nlist term typed\n')
            self.assertTrue(result.ok, result.error)
            self.assertIn('term c 0', result.output)

    def test_bare_sort_declaration_survives_load(self):
        with tempfile.TemporaryDirectory() as tmp:
            helper = os.path.join(tmp, 'categories.kurt')
            with open(helper, 'w') as stream:
                stream.write('sort nat\n')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            result = session.check_text('load categories\nlist sort categories\n')
            self.assertTrue(result.ok, result.error)
            self.assertIn('sort nat', result.output)
            self.assertIn('categories.kurt:1', result.output)

    def test_sort_and_symbol_names_cannot_clash_across_load(self):
        with tempfile.TemporaryDirectory() as tmp:
            sorted_file = os.path.join(tmp, 'sorted.kurt')
            symbol_file = os.path.join(tmp, 'symbol.kurt')
            with open(sorted_file, 'w') as stream:
                stream.write('sort object\nobject c\nbool P\narity P 1\nuse P c "typed"\n')
            with open(symbol_file, 'w') as stream:
                stream.write('bool object\nuse object "object-fact"\n')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            first_symbol = session.check_text('load symbol\nload sorted\n')
            first_sort = session.check_text('load sorted\nload symbol\n')
            self.assertFalse(first_symbol.ok)
            self.assertFalse(first_sort.ok)
            self.assertIn('term symbol', first_symbol.error or '')
            self.assertIn('sort here', first_sort.error or '')

    def test_untyped_kurt_is_unchanged(self):
        result = kurt.check_text('bool P\narity P 1\nuse P a\n')
        self.assertTrue(result.ok, result.error)

    def test_schema_matching_preserves_declared_sorts(self):
        source = (
            'sort nat, vec\n'
            'var n, v\n'
            'nat n\n'
            'vec v\n'
            'bool P 0\n'
            'arity P 1\n'
            'bool Q\n'
            'use (P n) implies Q "nat-only"\n'
            'use P v "vector-fact"\n'
            'Q\n'
        )
        result = kurt.check_text(source)
        self.assertFalse(result.ok)
        self.assertIn('can not derive `Q`', result.error or '')

    def test_exported_schema_matching_preserves_declared_sorts(self):
        with tempfile.TemporaryDirectory() as tmp:
            helper = os.path.join(tmp, 'nat-rule.kurt')
            with open(helper, 'w') as stream:
                stream.write(
                    'sort nat\nvar n\nnat n\nbool P 0\narity P 1\nbool Q\n'
                    'use (P n) implies Q "nat-only"\n'
                )
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            result = session.check_text(
                'sort vec\nvar v\nvec v\nload nat-rule\nuse P v "vector-fact"\nQ\n'
            )
            self.assertFalse(result.ok)
            self.assertIn('can not derive `Q`', result.error or '')

    def test_completion_includes_declared_sort(self):
        shell = core.Shell()
        self.assertTrue(shell.start_text('sort natural\nbreakpoint\n').ok)
        self.assertIn('natural', shell.completions('nat', 'nat'))

    def test_lambda_paper_typing_notation_is_sorted(self):
        good = kurt.check_text(
            'load lambda\n'
            '(extend empty base) ⊢ (at zero) : base\n'
            'empty ⊢ (abs base (at zero)) : (fun base base)\n'
            'empty ⊢ (λ x x) : (fun base base)\n'
        )
        self.assertTrue(good.ok, good.error)

        bad = kurt.check_text('load lambda\nempty ⊢ base : unit\n')
        self.assertFalse(bad.ok)
        self.assertIn('must have sort `term`', bad.error or '')

    def test_binding_operator_propagates_sort_to_bound_variable(self):
        good = kurt.check_text(
            'sort term\narity λ 2\nbindop λ\nterm λ 0 1 2\n'
            'bool P 0\narity P 1\nuse P (λ x x)\n'
        )
        self.assertTrue(good.ok, good.error)

        bad = kurt.check_text(
            'sort term\narity λ 2\nbindop λ\nterm λ 0 1 2\n'
            'const c\nbool P 0\narity P 1\nuse P (λ x c)\n'
        )
        self.assertFalse(bad.ok)
        self.assertIn('must have sort `term`', bad.error or '')

    def test_later_grammar_declaration_revalidates_sort_signature(self):
        result = kurt.check_text('sort term\nterm f 2\narity f 1\n')
        self.assertFalse(result.ok)
        self.assertIn('more than 1 arg', result.error or '')


if __name__ == '__main__':
    unittest.main()
