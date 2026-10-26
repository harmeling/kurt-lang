import builtins
import copy
import io
import contextlib
import unittest

import kurt.kurt as kurt

# in the shell, a line that fails is reported, and the session goes on as if the line had not
# been typed (found in the soundness review of 2026-09-29: some failing lines killed the shell
# with a traceback, or left it in a wrong indentation or chain state)


def shell(lines: list[str]) -> tuple[str, str]:
    # run `lines` as typed into the shell, and return what it printed to stdout and stderr
    feed = iter(lines)
    def fake_input(prompt=''):
        try:
            return next(feed)
        except StopIteration:
            raise EOFError from None
    old_input = builtins.input
    builtins.input = fake_input
    stdin = io.StringIO()
    stdin.name = '<stdin>'
    out, err = io.StringIO(), io.StringIO()
    try:
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            kurt.read_eval_loop(stdin, copy.deepcopy(kurt.initial_kb))
    finally:
        builtins.input = old_input
    return out.getvalue(), err.getvalue()


def at_the_top(out: str) -> bool:
    # `summary` (the last line typed) shows no open block
    summary = [line for line in out.splitlines() if line.startswith('; ')]
    return bool(summary) and not any(line.startswith('; open:') for line in summary)


class TestShellErrors(unittest.TestCase):
    def test_line_after_a_confirmed_expect_fails_again(self):
        # the line closing the `expect` is evaluated again, and fails again: an error, not a traceback
        out, err = shell(['load logic', 'prop A, C', 'expect "ProofError"', '    let x', '        const h',
                          '        todo A h', 'C', 'A implies A'])
        self.assertIn('confirmed', out)
        self.assertIn('can not derive `C`', err)
        self.assertIn('A implies A', out)                       # the session went on (before `Bye!`)

    def test_failed_chain_step_can_be_typed_again(self):
        out, err = shell(['load numbers', 'const a, b, c', 'use a < b', 'use b = c', 'a < b',
                          '  = a', '  = c', 'a < c'])
        self.assertEqual(err.count('Error'), 1, err)             # only `= a`
        self.assertIn('by chain', out)

    def test_failed_line_keeps_the_block(self):
        out, err = shell(['load propositional', 'prop A, B', 'assume A', '    B', '    A', 'A implies A', 'summary'])
        self.assertEqual(err.count('Error'), 1, err)             # only `B`
        self.assertIn('A implies A', out)
        self.assertTrue(at_the_top(out), out)

    def test_expect_that_never_raises_does_not_get_the_shell_stuck(self):
        # reported bug: `expect "ProofError" / true` (no error at all) left the shell stuck at
        # the block's indentation forever, re-raising the same `ExpectationError` on every later
        # line, however unrelated (even `summary`)
        out, err = shell(['load propositional', 'prop A', 'expect "ProofError"', '    true', 'true', 'A implies A', 'summary'])
        self.assertEqual(err.count('ExpectationError'), 1, err)
        self.assertIn('A implies A', out)                       # the session went on (before `Bye!`)
        self.assertTrue(at_the_top(out), out)

    def test_several_picks_on_one_line(self):
        out, err = shell(['load logic, equality', 'const a', 'exists y (y = a)',
                          'pick c with c = a, d with d = a', 'a = a', 'summary'])
        self.assertIn('one `pick` per line', err)
        self.assertEqual(err.count('Error'), 1, err)
        self.assertTrue(at_the_top(out), out)

    def test_failed_first_line_of_a_block(self):
        # the block is open, with the indentation of that line: the next line can close it.
        # The dedent (`true`) can't raise the expected `ProofError` either, so -- like a
        # `confirmed` expect -- the whole block is discarded right then, not left open (found in
        # the same hunt as the module docstring's issue: this one left the shell permanently
        # stuck, re-raising the same `ExpectationError` for every following line).
        out, err = shell(['load propositional', 'expect "ProofError"', '    local', 'true', 'summary'])
        self.assertIn('got a different error', err)                    # a `ParseError`
        self.assertEqual(err.count('ExpectationError'), 1, err)        # `true` can't close the block
        self.assertTrue(at_the_top(out), out)


class TestLatexShortcuts(unittest.TestCase):
    def test_only_whole_commands(self):
        # `\b` is the modal box shortcut, but `\bot` was replaced by `□ot`
        self.assertEqual(kurt.replace_latex_syntax(r'\b A'), '□ A')
        self.assertEqual(kurt.replace_latex_syntax(r'\cap\cup'), '∩∪')
        for command in (r'\boxed', r'\div', r'\bigcup'):
            self.assertEqual(kurt.replace_latex_syntax(command), command)
        self.assertEqual(kurt.replace_latex_syntax(r'\bot'), '⊥')     # since 2026-10-14 a command of its own (LaTeX's)


if __name__ == '__main__':
    unittest.main()
