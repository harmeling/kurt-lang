import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

PROOF = 'load prop\nbool A, B\nuse A implies B\nuse A\nB\n'
UNDECLARED = 'load prop\nuse A\nA\n'          # `A` not declared: an error only with `strict`


class TestApi(unittest.TestCase):
    # `check_text`, `check_file`, and sessions with their own options and state

    def test_check_text(self):
        result = kurt.check_text(PROOF)
        self.assertTrue(result.ok and result.complete)
        self.assertIn('; 5 by 3(4)', result.output)
        self.assertIn('Proof checked', result.output)
        failed = kurt.check_text('load prop\nbool A, B\nB\n', name='mine.kurt')
        self.assertFalse(failed.ok)
        self.assertEqual(failed.error_kind, 'ProofError')
        self.assertIn('mine.kurt', failed.error)
        with_todo = kurt.check_text('load prop\nbool A\ntodo A\n')
        self.assertTrue(with_todo.ok)
        self.assertFalse(with_todo.complete)

    def test_check_file(self):
        result = kurt.check_file(str(PROJECT_ROOT / 'proofs' / 'natural-deduction' / 'contraposition.kurt'))
        self.assertTrue(result.complete, result.error)
        self.assertIn('; 26 by or-elim(25, 11-13, 14-15)', result.output)

    def test_the_same_text_gives_the_same_output_in_any_session(self):
        first, second = kurt.new_session(), kurt.new_session()
        a = first.check_text(PROOF).output
        first.check_text('load logic\nconst a\nuse ∀ $x ($x = $x)\na = a\n')    # uses fresh names
        self.assertEqual(second.check_text(PROOF).output, a)
        self.assertEqual(kurt.new_session().check_text(PROOF).output, a)

    def test_options_stay_in_their_session(self):
        strict = kurt.new_session(kurt.RunConfig(strict=True))
        self.assertFalse(strict.check_text(UNDECLARED).ok)
        self.assertTrue(kurt.check_text(UNDECLARED).ok)          # another session: not strict
        self.assertFalse(strict.check_text(UNDECLARED).ok)       # and the strict one still is
        self.assertFalse(kurt.strict_mode)                       # the module's own state is back

    def test_sessions_can_alternate(self):
        # one session's checks, interleaved with another's, end in the same state (fresh names,
        # certificates) as alone
        text = 'load logic\nconst a\nuse ∀ $x ($x = $x)\na = a\n'
        alone = kurt.new_session()
        alone.check_text(PROOF)
        expected = alone.check_text(text).output
        one, other = kurt.new_session(), kurt.new_session()
        other.check_text(PROOF)
        one.check_text(PROOF)
        other.check_text('load set\nconst a\nuse ∀ $y ($y ∈ ∅ ⇒ $y = a)\n')
        self.assertEqual(one.check_text(text).output, expected)
        self.assertEqual(one._state['counters'], alone._state['counters'])
        self.assertEqual(sorted(one._state['certificates_by_line']), sorted(alone._state['certificates_by_line']))
        self.assertNotEqual(other._state['counters'], alone._state['counters'])

if __name__ == '__main__':
    unittest.main()
