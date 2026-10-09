import json
import unittest

import kurt


class TestFailureExplanations(unittest.TestCase):
    def test_missing_premise_is_structured_and_rendered(self):
        result = kurt.check_text('bool A, B\nuse A implies B "mp"\nB\n')
        self.assertFalse(result.ok)
        self.assertEqual(result.failure, {
            'kind': 'not-derived',
            'goal': 'B',
            'summary': 'no one-step derivation was found',
            'candidates': [{
                'rule': 'mp',
                'location': 'line 2',
                'missing': ['A'],
                'matched': [],
            }],
        })
        self.assertIn('`mp` (line 2): missing `A`', result.error or '')
        self.assertEqual(result.events[-1]['failure'], result.failure)
        self.assertEqual(json.loads(result.to_json())['failure'], result.failure)

    def test_reports_present_and_missing_parts_of_a_premise(self):
        result = kurt.check_text(
            'load prop\nbool A, B, C\nuse A and B implies C "both"\nuse A\nC\n')
        candidate = result.failure['candidates'][0]
        self.assertEqual((candidate['rule'], candidate['missing']), ('both', ['B']))
        self.assertEqual(candidate['matched'], ['line 4'])

    def test_success_has_no_failure_explanation(self):
        result = kurt.check_text('bool A, B\nuse A implies B\nuse A\nB\n')
        self.assertTrue(result.ok)
        self.assertIsNone(result.failure)

    def test_number_of_suggestions_is_bounded(self):
        result = kurt.check_text(
            'bool A, B\n'
            'use A implies B "one"\nuse A implies B "two"\n'
            'use A implies B "three"\nuse A implies B "four"\nB\n')
        self.assertLessEqual(len(result.failure['candidates']), 3)

    def test_failed_goal_uses_source_variable_names(self):
        result = kurt.check_text('var x\nconst P\nP x\n')
        self.assertFalse(result.ok)
        self.assertEqual(result.failure['goal'], 'P x')
        self.assertIn('can not derive `P x`', result.error or '')
        self.assertNotIn('$$', result.error or '')
        self.assertNotIn('%%', result.error or '')


if __name__ == '__main__':
    unittest.main()
