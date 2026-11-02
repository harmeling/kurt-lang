import unittest

import kurt.kurt as kurt


class TestVarTwice(unittest.TestCase):
    def test_a_repeated_var_is_an_error(self):
        # (2026-11-02: like `const`; before, the second `var x` was accepted silently)
        result = kurt.check_text('var x\nvar x\n')
        self.assertFalse(result.ok)
        self.assertIn('already a variable', result.error or '')

    def test_a_variable_in_a_nested_level_is_a_new_one(self):
        result = kurt.check_text('load logic\nvar x\nshow true\nproof\n    true\nqed\n')
        self.assertTrue(result.ok, result.error)


if __name__ == '__main__':
    unittest.main()
