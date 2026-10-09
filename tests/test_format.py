import unittest

import kurt.kurt as kurt


class TestFormat(unittest.TestCase):
    def test_source_preserves_formula_spelling(self):
        source = kurt.check_text(
            'load prop\n'
            'bool A, B\n'
            'format source\n'
            'use B ∧ A\n'
        )
        normal = kurt.check_text(
            'load prop\n'
            'bool A, B\n'
            'use B ∧ A\n'
        )

        self.assertTrue(source.ok, source.error)
        self.assertIn('use B ∧ A', source.output)
        self.assertTrue(normal.ok, normal.error)
        self.assertIn('use A ∧ B', normal.output)

    def test_original_name_is_rejected_after_rename(self):
        result = kurt.check_text('format original\n')
        self.assertFalse(result.ok)
        self.assertIn('format source', result.error or '')


if __name__ == '__main__':
    unittest.main()
