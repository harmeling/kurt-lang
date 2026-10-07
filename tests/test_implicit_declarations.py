import unittest

import kurt.kurt as kurt


class TestImplicitDeclarations(unittest.TestCase):
    def test_syntax_declaration_still_reports_the_constant_inferred_by_first_use(self):
        result = kurt.check_text(
            'load set\n'
            'infix ∘ 70 70\n'
            'const G, e, inv\n'
            'use $a ∈ G ∧ $b ∈ G ⇒ $a ∘ $b ∈ G "G-closed"\n'
        )

        self.assertTrue(result.ok, result.error)
        self.assertIn('const ∘', result.output)
        declaration = next(event for event in result.events if event['text'] == 'const ∘')
        self.assertEqual((declaration['kind'], declaration['reason']), ('declaration', 'added constant'))

    def test_first_use_reports_all_inferred_declarations(self):
        result = kurt.check_text('use P a\n')

        self.assertTrue(result.ok, result.error)
        declarations = [(event['text'], event['reason']) for event in result.events
                        if event['kind'] == 'declaration']
        self.assertEqual(declarations, [
            ('const P', 'added constant'),
            ('const a', 'added constant'),
            ('bool P 0', 'added boolean signature'),
        ])
        self.assertNotIn('new constant', result.output)

    def test_explicit_roles_and_definitions_are_not_reported_twice(self):
        variable = kurt.check_text(
            'load equality\n'
            'infix ∘ 70 70\n'
            'var ∘\n'
            'use $a ∘ $b = $a ∘ $b\n'
        )
        definition = kurt.check_text('load equality\ndef c = a\n')

        self.assertTrue(variable.ok, variable.error)
        self.assertNotIn('const ∘', variable.output)
        self.assertTrue(definition.ok, definition.error)
        self.assertNotIn('const c', definition.output)
        self.assertNotIn('bool c', definition.output)
        self.assertIn('const a', definition.output)


if __name__ == '__main__':
    unittest.main()
