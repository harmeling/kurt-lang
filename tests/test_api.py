import json
import os
import subprocess
import tempfile
import sys
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT, numbered

PROOF = 'load prop\nbool A, B\nuse A implies B\nuse A\nB\n'
UNDECLARED = 'load prop\nuse A\nA\n'          # `A` not declared: an error only with `strict`


class TestApi(unittest.TestCase):
    # `check_text`, `check_file`, and sessions with their own options and state

    def test_check_text(self):
        result = kurt.check_text(PROOF)
        self.assertTrue(result.ok and result.complete)
        self.assertTrue(numbered(result.output, 5, 'by 3(4)'), result.output)
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
        self.assertTrue(numbered(result.output, 26, 'by case-elim(25, 11-13, 14-15)'), result.output)

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
        self.assertFalse(kurt.run_state.strict_mode)                       # the module's own state is back

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
        self.assertEqual((one._state.var_counter, one._state.bool_var_counter), (alone._state.var_counter, alone._state.bool_var_counter))
        self.assertEqual(sorted(one._state.certificates_by_line), sorted(alone._state.certificates_by_line))
        self.assertNotEqual((other._state.var_counter, other._state.bool_var_counter), (alone._state.var_counter, alone._state.bool_var_counter))

    def test_a_text_is_never_trusted_by_its_name(self):
        # trust comes from where a file was read: under `strict`, a text named like a theory of
        # Kurt or like a file in a `-p` directory may still not `use` (dev/astra-suggestions.md, 2)
        with tempfile.TemporaryDirectory() as teacher:
            session = kurt.new_session(kurt.RunConfig(strict=True, paths=[teacher]))
            names = ['<embedded>/student.kurt', '<embedded>/prop.kurt', '<chain transitivity for [<]>',
                     os.path.join(teacher, 'student.kurt'), str(kurt.packaged_theory_file('prop.kurt'))]
            for name in names:
                with self.subTest(name=name):
                    self.assertFalse(session.check_text('use false\nfalse\n', name=name).ok)
            with open(os.path.join(teacher, 'axioms.kurt'), 'w') as f:
                f.write('bool C\nuse C "c"\n')
            self.assertTrue(session.check_text('load axioms\nC\n').ok)    # a file there still is
        for name in ('<stdin>', '<shell>'):                                # the shell's names
            self.assertRaises(ValueError, kurt.check_text, 'A\n', name=name)

    def test_a_text_leaves_kurtc_on(self):
        # `check_text` writes no `.kurtc`, but the next file of the session does (finding 5)
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'p.kurt')
            with open(path, 'w') as f:
                f.write(PROOF)
            session = kurt.new_session(kurt.RunConfig(kurtc=True))
            self.assertTrue(session.check_text(PROOF).ok)
            self.assertTrue(session.check_file(path).ok)
            self.assertTrue(os.path.exists(path + 'c'))

    def test_restating_a_labelled_fact_is_a_step(self):
        # the events come from the reasons as data, not from parsing their text: `by "lbl"` was
        # read as a line with the label `lbl` (2026-10-09)
        result = kurt.check_text('load prop\nbool A\nuse A "given"\nA\n')
        event = [e for e in result.events if e.get('id') == '4'][0]
        self.assertEqual((event['kind'], event['rule'], event['uses']), ('step', 'given', []))
        self.assertNotIn('label', event)

    def test_the_todos_before_an_error_count(self):
        # an editor marks them, also when a later line fails (2026-10-09: they were lost)
        result = kurt.check_text('load prop\nbool A, B, C\nuse A\ntodo A and C\nA and C\nB\n')
        self.assertFalse(result.ok)
        self.assertEqual(len(result.todos), 1)
        self.assertIn(':4 todo A and C', result.todos[0])

    def test_the_todos_before_an_unfinished_proof_count(self):
        # the error at the end of the file (a proof that isn't finished) keeps the todos before it
        result = kurt.check_text('load prop\nbool A, B, C\nuse A\ntodo A and C\nshow B or C\nproof\n    A\n')
        self.assertEqual((result.error_kind, result.error_line), ('ProofError', 5))
        self.assertIn("isn't finished at the end of the file", result.error)
        self.assertEqual(len(result.todos), 1)

    def test_events(self):
        # each printed line as a record: its line, id, kind, rule and the lines it uses
        result = kurt.check_text('load prop\nbool A, B\nuse A implies B   "rule"\nuse A\nB    ; modus ponens\n'
                                 'assume A\n    B\nshow B\nproof\n    B\nqed\nC\n')
        events = {(e['id'], e['kind']): e for e in result.events}
        self.assertEqual(events[('3', 'assumed')]['label'], 'rule')
        self.assertEqual(events[('3', 'assumed')]['text'], 'use A implies B "rule"')
        self.assertIn('use A implies B "rule"', result.output)
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


    def test_a_shell_continues_where_the_check_stopped(self):
        failing = 'load prop\nbool A, B\nuse A\nuse A implies B\nshow A and B\nproof\n    B\n    A and C\nqed\n'
        shell = kurt.Shell()
        result = shell.start_text(failing)
        self.assertFalse(result.ok)
        self.assertEqual((shell.stopped, shell.line, shell.indentation()), ('error', 8, 4))   # at the failing line
        self.assertIn('; to prove: A and B', shell.summary())
        self.assertTrue(numbered(shell.feed('    A and B'), 8, 'by and-intro'))
        self.assertEqual(shell.next_steps(), ['qed'])
        self.assertTrue(numbered(shell.feed('qed'), 9, 'by 8'))
        self.assertEqual(shell.accepted, ['    A and B', 'qed'])
        self.assertIn('can not derive', shell.feed('C'))                 # an error is shown, the shell goes on
        self.assertTrue(numbered(shell.feed('A'), 11, 'by proof.kurt:3'))

    def test_a_shell_after_the_end_and_at_a_breakpoint(self):
        shell = kurt.Shell()
        shell.start_text('load numbers\ncalc on\nconst x\nuse x = 3\n')
        self.assertEqual(shell.stopped, 'end')
        self.assertEqual(shell.completions('17*42=', ''), ['714'])
        self.assertTrue(numbered(shell.feed('x = 3'), 5, 'by proof.kurt:4'))
        shell = kurt.Shell()
        shell.start_text('load prop\nbool A\nuse A\nshow A and A\nproof\n    breakpoint\n    A and A\nqed\n')
        self.assertEqual((shell.stopped, shell.line), ('breakpoint', 7))
        self.assertEqual(shell.next_steps(), ['A and A'])               # inside the proof, as it was there


if __name__ == '__main__':
    unittest.main()
