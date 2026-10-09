import copy
import unittest

import kurt.kurt as kurt


class TestDeepLogicEncodings(unittest.TestCase):
    def test_pretty_logic_aliases_are_theory_local(self):
        core = copy.deepcopy(kurt.initial_kb)
        for alias in ('⊤', '⇒', '∧', '∨', '¬', '∀', '∃'):
            self.assertIsNone(core.get_alias(alias), alias)

        prop = kurt.load_file('prop.kurt', copy.deepcopy(kurt.initial_kb), main=False)
        self.assertEqual(prop.get_alias('⊤'), 'true')
        self.assertEqual(prop.get_alias('⇒'), 'implies')
        self.assertEqual(prop.get_alias('∧'), 'and')
        self.assertEqual(prop.get_alias('∨'), 'or')
        self.assertEqual(prop.get_alias('¬'), 'not')
        self.assertIsNone(prop.get_alias('∀'))

        logic = kurt.load_file('logic.kurt', copy.deepcopy(kurt.initial_kb), main=False)
        self.assertEqual(logic.get_alias('∀'), 'forall')
        self.assertEqual(logic.get_alias('∃'), 'exists')

    def test_deep_language_can_own_pretty_logic_glyphs(self):
        result = kurt.check_text(
            'sort formula\n'
            'prefix ¬ 70\n'
            'infix ∧ 50 50, ∨ 40 40\n'
            'const ¬, ∧, ∨\n'
            'formula ¬ 0 1, ∧ 0 1 2, ∨ 0 1 2\n'
            'const P, Q\nformula P, Q\n'
        )
        self.assertTrue(result.ok, result.error)

    def test_vdash_shortcut_and_scanner(self):
        self.assertEqual(kurt.replace_latex_syntax(r'\vdash A'), '⊢ A')
        tokens = list(kurt.scan_string('⊢ A', copy.deepcopy(kurt.initial_kb)))
        self.assertEqual(tokens[0].value, '⊢')

    def test_greek_variable_names(self):
        kb = copy.deepcopy(kurt.initial_kb)
        tokens = list(kurt.scan_string('$Γ %φ $Γ2', kb))
        self.assertEqual([token.value for token in tokens[:3]], ['$Γ', '%φ', '$Γ2'])
        result = kurt.check_text('var Γ\nuse Γ implies Γ "greek"\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('; schema: %Γ implies %Γ', result.output)

    def test_modal_turnstile_is_prefix_and_infix(self):
        kb = kurt.load_file('modal.kurt', copy.deepcopy(kurt.initial_kb), main=False)
        self.assertTrue(kb.is_prefix('⊢'))
        self.assertTrue(kb.is_infix('⊢'))
        self.assertTrue(kb.is_const('⊢'))
        self.assertEqual(kb.bool_sig('⊢'), [0])

    def test_necessitation_and_empty_context_bridge(self):
        result = kurt.check_text(
            'load modal\n'
            'const P, Q\n'
            'formula P, Q\n'
            '⊢ (P → (Q → P))\n'
            '⊢ □(P → (Q → P))\n'
            'empty ⊢ □(P → (Q → P))\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('by necessitation', result.output)
        self.assertIn('by theorem-to-empty-sequent', result.output)

    def test_object_formulas_are_terms(self):
        kb = kurt.load_file('modal.kurt', copy.deepcopy(kurt.initial_kb), main=False)
        expr = kurt.parse_expression(kurt.PeekableGenerator(kurt.scan_string('P → Q', kb)),
                                     kb, kurt.begin_rbp)
        expr, _, _ = kurt.post_process(kb, expr)
        self.assertFalse(kurt.bool_expr(expr, kb))
        self.assertTrue(kurt.sort_expr(expr, 'formula', kb))
        self.assertTrue(kurt.bool_expr(
            kurt.post_process(kb, kurt.parse_expression(
                kurt.PeekableGenerator(kurt.scan_string('⊢ (P → Q)', kb)),
                kb, kurt.begin_rbp))[0],
            kb,
        ))


if __name__ == '__main__':
    unittest.main()
