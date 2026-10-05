import unittest

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
        out = self.output('load arith\ncalc on\nconst x\nuse x = 0 - 8\n')
        self.assertIn('use x = (-8)', out)             # not `-8`, which could read as `- 8`


if __name__ == '__main__':
    unittest.main()
