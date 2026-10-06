import json
import subprocess
import sys
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

    def test_events(self):
        # each printed line as a record: its line, id, kind, rule and the lines it uses
        result = kurt.check_text('load prop\nbool A, B\nuse A implies B   "rule"\nuse A\nB    ; modus ponens\n'
                                 'assume A\n    B\nshow B\nproof\n    B\nqed\nC\n')
        events = {(e['id'], e['kind']): e for e in result.events}
        self.assertEqual(events[('3', 'assumed')]['label'], 'rule')
        step = events[('5', 'step')]
        self.assertEqual((step['line'], step['rule'], step['uses'], step['comment']), (5, 'rule', ['4'], 'modus ponens'))
        self.assertEqual(events[('6-7', 'step')]['rule'], 'impl-intro')       # the result of the block
        self.assertEqual(events[('6', 'open')]['text'], 'assume A')
        self.assertEqual(events[('8', 'claim')]['text'], 'show B')
        self.assertEqual(events[('7', 'step')]['level'], 1)
        self.assertEqual(result.events[-1]['kind'], 'error')
        self.assertEqual((result.error_line, result.error_kind), (12, 'ProofError'))
        done = kurt.check_text(PROOF)
        self.assertEqual(done.events[-1], {'line': None, 'id': None, 'kind': 'text', 'level': 0, 'text': 'Proof checked', 'reason': ''})

    def test_json_on_the_command_line(self):
        def run(text):
            path = PROJECT_ROOT / 'tests' / 'json-test.kurt'
            path.write_text(text)
            try:
                return subprocess.run([sys.executable, str(PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py'), '--json', '--no-kurtc', str(path)],
                                      capture_output=True, text=True, cwd=PROJECT_ROOT)
            finally:
                path.unlink()
        good = run(PROOF)
        self.assertEqual(good.returncode, 0)
        data = json.loads(good.stdout)
        self.assertTrue(data['ok'] and data['complete'])
        self.assertIn({'rule': '3', 'uses': ['4']}, [{'rule': e.get('rule'), 'uses': e.get('uses')} for e in data['events']])
        bad = run('load prop\nbool A\nA\n')
        self.assertEqual(bad.returncode, 1)
        self.assertEqual(json.loads(bad.stdout)['error_line'], 3)


if __name__ == '__main__':
    unittest.main()
