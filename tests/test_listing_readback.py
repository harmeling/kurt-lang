import unittest

import kurt.kurt as kurt


class TestListingReadsBack(unittest.TestCase):
    def test_a_listed_binder_has_its_power(self):
        # (2026-11-02: `binder forall` was listed without the 17 of `binder forall 17`)
        result = kurt.check_text('load logic\nlist binder logic\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('binder forall 17 ', result.output)

    def test_a_listed_binder_declares_the_same(self):
        result = kurt.check_text('arity big 2\nbinder big 30\nsyntax big\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('binder big 30', result.output)


if __name__ == '__main__':
    unittest.main()
