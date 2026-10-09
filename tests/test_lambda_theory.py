import unittest

import kurt


class TestLambdaTheory(unittest.TestCase):
    def test_typing_application_and_beta(self):
        result = kurt.check_text(
            'load lambda\n'
            'has (extend empty base) (at zero) base\n'
            'has empty (abs base (at zero)) (fun base base)\n'
            'has empty (app (abs base (at zero)) unit) base\n'
            'has empty (λ x x) (fun base base)\n'
            '(app (λ x x) unit) ↦ unit\n'
            '(app (λ x x) unit) ⇝ unit\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('by variable-zero', result.output)
        self.assertIn('by abstraction', result.output)
        self.assertIn('by named-identity', result.output)
        self.assertIn('by application', result.output)
        self.assertIn('by beta', result.output)
        self.assertIn('by cbv-beta', result.output)

    def test_beta_avoids_capture(self):
        result = kurt.check_text(
            'load lambda\n'
            'var y\n'
            'term y\n'
            '(app (λ x (λ y x)) y) ↦ (λ z y)\n'
        )
        self.assertTrue(result.ok, result.error)

    def test_malformed_typing_judgment_is_rejected_by_sorts(self):
        result = kurt.check_text('load lambda\nhas empty base base\n')
        self.assertFalse(result.ok)
        self.assertIn('must have sort `term`', result.error or '')


if __name__ == '__main__':
    unittest.main()
