import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt


class TestExportedVariables(unittest.TestCase):
    def check_files(self, helper: str, main: str) -> kurt.CheckResult:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'schemas.kurt').write_text(helper, encoding='utf-8')
            return kurt.check_text(main, name=str(root / 'main.kurt'))

    def test_named_boolean_variables_stay_schematic_after_load(self):
        result = self.check_files(
            'load prop\nvar p, q\nuse (p implies q) implies (p implies q) "schema"\n',
            'bool p, q\nconst p, q\nload schemas\nbool A, B\n(A implies B) implies (A implies B)\n',
        )
        self.assertTrue(result.ok, result.error)

    def test_plain_variable_names_and_inferred_types_do_not_cross(self):
        result = self.check_files(
            'load prop\nvar p, q\nuse p and q "pq"\n',
            'load schemas\nbool p, q\nconst p, q\nbool A, B\nA and B\n',
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('A and B', result.output)

    def test_named_infix_operator_and_terms_stay_schematic_after_load(self):
        result = self.check_files(
            'load equality\nvar x, y, op\ninfix op 55 55\n'
            'use x op y = y op x "commutative-variable-operator"\n',
            'load schemas\nconst a, b, star\ninfix star 55 55\n'
            'a star b = b star a\n',
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('a star b', result.output)

    def test_named_function_and_term_stay_schematic_after_load(self):
        result = self.check_files(
            'load equality\nvar x, f\narity f 1\nuse f x = x "function-variable"\n',
            'load schemas\nconst a, g\narity g 1\ng a = a\n',
        )
        self.assertTrue(result.ok, result.error)

    def test_named_prefix_operator_and_term_stay_schematic_after_load(self):
        result = self.check_files(
            'load equality\nvar x, op\nprefix op 80\nuse op x = x "prefix-variable-operator"\n',
            'load schemas\nconst a, neg\nprefix neg 80\nneg a = a\n',
        )
        self.assertTrue(result.ok, result.error)

    def test_named_postfix_operator_and_term_stay_schematic_after_load(self):
        result = self.check_files(
            'load equality\nvar x, op\npostfix op 80\nuse x op = x "postfix-variable-operator"\n',
            'load schemas\nconst a, bang\npostfix bang 80\na bang = a\n',
        )
        self.assertTrue(result.ok, result.error)

    def test_use_reports_stable_schema_for_named_terms_and_operator(self):
        result = kurt.check_text(
            'load equality\n'
            'var x, y, ∘\n'
            'infix ∘ 55 55\n'
            'use x ∘ y = y ∘ x "comm"\n'
        )
        self.assertTrue(result.ok, result.error)
        schema = '$x $op $y = $y $op $x'
        self.assertIn(f'; schema: {schema}', result.output)
        event = next(event for event in result.events if event.get('label') == 'comm')
        self.assertEqual(event.get('schema'), schema)

    def test_schema_distinguishes_boolean_variables_and_preserves_source_comment(self):
        result = kurt.check_text(
            'load prop\n'
            'var p, q\n'
            'use p implies q "rule" ; source note\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('; schema: %p implies %q', result.output)
        self.assertIn(f'\n{"":<48}; source note', result.output)      # (42, after the line numbers)
        self.assertIn(f'\n{"":<48}; without proof "rule"', result.output)

    def test_schema_names_do_not_collide_with_explicit_schema_variables(self):
        result = kurt.check_text(
            'load equality\n'
            'var x, ∘\n'
            'infix ∘ 55 55\n'
            'use x ∘ $x = $x ∘ x "mixed"\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('; schema: $x2 $op $x = $x $op $x2', result.output)

    def test_format_source_does_not_add_generated_schema(self):
        result = kurt.check_text(
            'format source\n'
            'load equality\n'
            'var x, y, ∘\n'
            'infix ∘ 55 55\n'
            'use x ∘ y = y ∘ x "comm"\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertNotIn('schema:', result.output)

    def test_use_listing_repeats_the_effective_schema(self):
        result = kurt.check_text(
            'load equality\n'
            'var x, y, ∘\n'
            'infix ∘ 55 55\n'
            'use x ∘ y = y ∘ x "comm"\n'
            'use\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertEqual(result.output.count('; schema: $x $op $y = $y $op $x'), 2)


if __name__ == '__main__':
    unittest.main()
