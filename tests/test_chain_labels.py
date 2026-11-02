import unittest

import kurt.kurt as kurt


class TestChainLabels(unittest.TestCase):
    # the rules a `chain` generates are named after the two relations, "chain-trans-<=/<", and a pair that two
    # chains share (`=` with `=` in number.kurt's `chain = <= <` and `chain = >= >`) is generated once (2026-11-02)
    def labels(self, text):
        result = kurt.check_text(text + '\ntheory\n')
        self.assertTrue(result.ok, result.error)
        return [line.rsplit('"', 2)[-2] for line in result.output.splitlines() if '"chain-trans-' in line]

    def test_the_label_names_the_two_relations(self):
        labels = self.labels('load number')
        self.assertIn('chain-trans-<=/<', labels)
        self.assertIn('chain-trans-=/<', labels)

    def test_no_label_is_generated_twice(self):
        for text in ('load number', 'load propositional'):
            labels = self.labels(text)
            self.assertEqual(len(labels), len(set(labels)), labels)

    def test_a_step_cites_the_rule_by_its_relations(self):
        result = kurt.check_text('load number\nconst x, y, z\nuse x = y\nuse y < z\nx < z\n')
        self.assertTrue(result.ok, result.error)
        self.assertRegex(result.output, r'by chain-trans-(=/<|>/=)\(')      # (the rule of `chain = <= <` or of `chain = >= >`)


if __name__ == '__main__':
    unittest.main()
