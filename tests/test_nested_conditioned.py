import unittest

import kurt.kurt as kurt

# a fact with several quantifiers that have conditions, `∀ x ∈ V ∀ y ∈ V P`, is used in one line (todo 81): the instance for
# the first `∀` is derived and shown as a step of its own, each an ordinary "forall-cond-elim"; the failure says which
# condition is missing (todo 82)

HEAD = '''load logic, number
const V, a, b, c
set V
use ∀ x ∈ V ∀ y ∈ V (x - y = 2 * x - (x + y))   "V2"
'''


def check(text: str) -> kurt.CheckResult:
    return kurt.Session().check_text(HEAD + text)


class TestNestedConditioned(unittest.TestCase):
    def test_two_conditioned_quantifiers_in_one_line(self):
        result = check('use a ∈ V\nuse b ∈ V\na - b = 2 * a - (a + b)\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('forall-cond-elim(V2, ', result.output)           # the instance for `a`, a step of its own
        self.assertRegex(result.output, r'\d+a by forall-cond-elim')

    def test_three_with_a_condition_on_the_variable_before(self):
        result = kurt.Session().check_text('''load logic, number
const V, a, b, c
set V
use ∀ x ∈ V ∀ y > x ∀ z ∈ V (x - y - z = x - (y + z))   "V3"
use a ∈ V
use c ∈ V
use a < b
a - b - c = a - (b + c)
''')
        self.assertTrue(result.ok, result.error)
        self.assertRegex(result.output, r'\d+a .*forall-cond-elim')
        self.assertRegex(result.output, r'\d+b .*forall-cond-elim')

    def test_a_missing_condition_is_still_an_error_and_named(self):
        result = check('use a ∈ V\na - b = 2 * a - (a + b)\n')
        self.assertFalse(result.ok)
        self.assertEqual(result.error_kind, 'ProofError')
        self.assertIn('`V2` (line 4) has 2 quantifiers with conditions', result.error or '')
        self.assertIn('`b ∈ V` is not known', result.error or '')

    def test_the_steps_have_certificates_the_kernel_checks(self):
        result = kurt.Session().check_text(HEAD + 'use a ∈ V\nuse b ∈ V\na - b = 2 * a - (a + b)\n', certificates=True)
        self.assertTrue(result.ok, result.error)
        self.assertTrue(any('forall-cond-elim' in text for text in result.certificates.values()))
