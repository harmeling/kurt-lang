import unittest

import kurt.kurt as kurt


class TestEchoAsWritten(unittest.TestCase):
    # the echo of a line shows what the student wrote: the symbol of an alias (`∧`, also with its holes, `_∧_(A, B)`) and the
    # order of the operands of a symmetric operator (`B ∨ A`); the stored formula is the normalized one (decided 2026-11-02)
    def echoes(self, text):
        result = kurt.check_text(text)
        self.assertTrue(result.ok, result.error)
        return [event['text'] for event in result.events if event.get('kind') == 'step' or event.get('kind') == 'assumed']

    def test_the_operands_of_a_symmetric_operator_keep_their_order(self):
        lines = self.echoes('load propositional\nprop A, B\nuse A ∨ B\nB ∨ A\n')
        self.assertIn('B ∨ A', lines)

    def test_the_operands_of_a_sum_keep_their_order(self):
        result = kurt.check_text('load number\nconst a, b\nreal a, b\nuse a + b = b + a "comm"\nb + a = a + b\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('(b + a) = (a + b)', result.output)

    def test_an_alias_with_its_holes_is_shown_as_written(self):
        lines = self.echoes('load propositional\nprop A, B\nuse A ∧ B\n_∧_(A, B)\n')
        self.assertIn('A ∧ B', lines)
        self.assertNotIn('A and B', lines)


if __name__ == '__main__':
    unittest.main()
