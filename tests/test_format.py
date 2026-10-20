import unittest

import kurt.kurt as kurt


class TestFormat(unittest.TestCase):
    def test_source_preserves_formula_spelling(self):
        source = kurt.check_text(
            'load propositional\n'
            'prop A, B\n'
            'format source\n'
            'use B ∧ A\n'
        )
        normal = kurt.check_text(
            'load propositional\n'
            'prop A, B\n'
            'use B ∧ A\n'
        )

        self.assertTrue(source.ok, source.error)
        self.assertIn('use B ∧ A', source.output)
        self.assertTrue(normal.ok, normal.error)
        self.assertIn('use A ∧ B', normal.output)

    def test_without_argument_shows_the_value_and_the_others(self):
        # (2026-10-12: before, only `format normal`)
        result = kurt.check_text('format\nformat sexpr\nformat\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('the others: `format sexpr`, `format source`', result.output)
        self.assertIn('the others: `format normal`, `format source`', result.output)

    def test_original_name_is_rejected_after_rename(self):
        result = kurt.check_text('format original\n')
        self.assertFalse(result.ok)
        self.assertIn('format source', result.error or '')


if __name__ == '__main__':
    unittest.main()
