import builtins
import contextlib
import copy
import io
import unittest

import kurt.kurt as kurt

# a term on its own line continues on the next line, which starts with a relation of a chain (todo 80):
# `(a + b) * c` and, indented, `= a * c + b * c` are one statement; a term line without it is the old error,
# at the line of the term

HEAD = 'load number\nconst a, b, c\n'


def check(text: str, all_errors: bool = False) -> kurt.CheckResult:
    return kurt.Session(kurt.RunConfig(all_errors=all_errors)).check_text(HEAD + text)


class TestTermContinuation(unittest.TestCase):
    def test_a_term_and_its_continuation_are_a_statement(self):
        result = check('(a + b) * c\n    = a * c + b * c\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('by distrib-add', result.output)

    def test_the_chain_goes_on(self):
        result = check('(a + b) * c\n    = a * c + b * c\n    = c * a + b * c\n    = c * a + c * b\n')
        self.assertTrue(result.ok, result.error)

    def test_in_a_proof(self):
        result = check('show (a + b) * c = a * c + b * c\nproof\n    (a + b) * c\n        = a * c + b * c\nqed\n')
        self.assertTrue(result.ok, result.error)

    def test_a_term_with_nothing_after_it(self):
        result = check('a + b\n')
        self.assertFalse(result.ok)
        self.assertEqual(result.error_kind, 'EvalError')
        self.assertEqual(result.error_line, 3)
        self.assertIn('must be a statement', result.error or '')

    def test_a_term_followed_by_another_line(self):
        result = check('a + b\na = a\n')
        self.assertEqual(result.error_line, 3)          # (the term's line, not the next one)
        self.assertIn('must be a statement', result.error or '')

    def test_a_term_followed_by_a_line_that_is_not_indented(self):
        result = check('a + b\n= c\n')
        self.assertEqual(result.error_line, 3)

    def test_a_term_followed_by_a_block_keyword(self):
        result = check('show a = a\nproof\n    a + b\n    proof\n')
        self.assertEqual(result.error_line, 5)

    def test_all_errors_goes_on_and_reads_the_next_line(self):
        result = check('a + b\na = a\nb + c\nb = b\n', all_errors=True)
        self.assertEqual([e['line'] for e in result.errors], [3, 5])
        self.assertIn('a = a', result.output)       # (the line after the first error is checked)
        self.assertIn('b = b', result.output)

    def test_an_expect_around_a_term_line(self):
        result = check('expect "EvalError" "must be a statement"\n    a + b\na = a\n')
        self.assertTrue(result.ok, result.error)
        result = check('expect "EvalError" "must be a statement"\n    a + b\n')      # (the file ends after it)
        self.assertTrue(result.ok, result.error)

    def shell(self, lines):
        feed = iter(lines)
        def fake_input(prompt=''):
            try:
                return next(feed)
            except StopIteration:
                raise EOFError from None
        old, builtins.input = builtins.input, fake_input
        stdin = io.StringIO()
        stdin.name = '<stdin>'
        out, err = io.StringIO(), io.StringIO()
        try:
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                kurt.read_eval_loop(stdin, copy.deepcopy(kurt.initial_kb))
        finally:
            builtins.input = old
        return out.getvalue(), err.getvalue()

    def test_the_shell_takes_a_pasted_file(self):
        out, err = self.shell(['load number', 'const a, b, c', '(a + b) * c', '    = a * c + b * c'])
        self.assertEqual(err, '')
        self.assertIn('by distrib-add', out)

    def test_the_shell_reports_the_term_at_the_next_line(self):
        out, err = self.shell(['load number', 'const a, b', 'a + b', 'a = a'])
        self.assertIn('must be a statement', err)            # when the next line shows that nothing continues it
        self.assertIn('equal-intro', out)                    # and that line is read as usual

    def test_the_shell_reports_a_term_at_the_end(self):
        out, err = self.shell(['load number', 'const a, b', 'a + b'])
        self.assertIn('must be a statement', err)

    def test_json_events_of_the_lines(self):
        result = check('(a + b) * c\n    = a * c + b * c\n')
        lines = [event['line'] for event in result.events if event.get('reason')]
        self.assertIn(4, lines)            # the claim is at the line of its relation
