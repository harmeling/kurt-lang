import unittest

import kurt.kurt as kurt
import tests.test_kernel as test_kernel


class TestPrinting(unittest.TestCase):
    # how formulas are printed: as they are written, and so that they read back the same
    def output(self, text):
        return test_kernel.TestCertCommand.output(self, text)

    def test_comma_lists(self):
        out = self.output('load set\nbrackets ⟨ ⟩\nconst a, b, A\nuse ⟨a, b⟩ = a\nuse (a, b) ∈ A\nuse {a, b} = A\nuse ⟨a⟩ = b\n')
        self.assertIn('use ⟨a, b⟩ = a ', out)          # was `⟨ (a , b) ⟩`
        self.assertIn('use (a, b) ∈ A ', out)          # was `(a , b)`
        self.assertIn('use {a, b} = A ', out)
        self.assertIn('use ⟨a⟩ = b ', out)

    def test_negative_numbers(self):
        out = self.output('load numbers\ncalc on\nconst x\nuse x = 0 - 8\n')
        self.assertIn('use x = (0 - 8)', out)          # as written (since 2026-10-12, `calc` doesn't change a line)
        # a computed negative number (e.g. Tab after `0 - 8 =`): `(-8)`, not `-8`, which could read as `- 8`
        kb = kurt.copy.deepcopy(kurt.initial_kb)
        kurt.load_file('numbers.kurt', kb)               # (`=` an infix operator)
        equation = [kurt.Token('SYMBOL', '='), kurt.Token('SYMBOL', 'x'), kurt.Token('INT', -8)]
        self.assertEqual(kurt.expr_str(equation, kb), 'x = (-8)')


    def test_empty_brackets(self):
        # printed with Kurt's internal name `[$$$]` until 2026-10-14 (found by the soundness hunt)
        out = self.output('load matrix\ncalc on\n[] = []\n')
        self.assertIn('[] = []', out)
        self.assertNotIn('$$$', out)


if __name__ == '__main__':
    unittest.main()
