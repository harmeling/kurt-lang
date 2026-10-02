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
            raise EOFError
    old_input = builtins.input
    builtins.input = fake_input
    stdin = io.StringIO()
    stdin.name = '<stdin>'
    out, err = io.StringIO(), io.StringIO()
    try:
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            kurt.read_eval_loop(stdin, copy.deepcopy(kurt.initial_kb), mainstream=True)
    finally:
        builtins.input = old_input
    return out.getvalue(), err.getvalue()


class TestShellErrors(unittest.TestCase):
    def test_line_after_a_confirmed_expect_fails_again(self):
        # the line closing the `expect` is evaluated again, and fails again: an error, not a traceback
        out, err = shell(['load prop', 'bool A, C', 'expect "ProofError"', '    let x', '        const h',
                          '        todo A h', 'C', 'A implies A'])
        self.assertIn('confirmed', out)
        self.assertIn('can not derive `C`', err)
        self.assertIn('A implies A', out.splitlines()[-3])      # the session went on (before `Bye!`)

    def test_failed_chain_step_can_be_typed_again(self):
        out, err = shell(['load arith', 'const a, b, c', 'use a < b', 'use b = c', 'a < b',
                          '  = a', '  = c', 'a < c'])
        self.assertEqual(err.count('Error'), 1, err)             # only `= a`
        self.assertIn('by chain', out)

    def test_failed_line_keeps_the_block(self):
        out, err = shell(['load prop', 'bool A, B', 'assume A', '    B', '    A', 'A implies A', 'mode'])
        self.assertEqual(err.count('Error'), 1, err)             # only `B`
        self.assertIn('A implies A', out)
        self.assertIn('root', out.splitlines()[-3])

    def test_several_picks_on_one_line(self):
        out, err = shell(['load logic, equality', 'const a', 'exists y (y = a)',
                          'pick c with c = a, d with d = a', 'a = a', 'mode'])
        self.assertIn('one `pick` per line', err)
        self.assertEqual(err.count('Error'), 1, err)
        self.assertIn('root', out.splitlines()[-3])

    def test_failed_first_line_of_a_block(self):
        # the block is open, with the indentation of that line: the next line can close it
        # (the dedent can't close it, it has no `ProofError` -- so it stays open, until `break`)
        out, err = shell(['load prop', 'expect "ProofError"', '    local', 'true', '    break', 'mode'])
        self.assertIn('got a different error', err)                    # a `SyntaxError`
        self.assertNotIn('expected increased indentation', err)
        self.assertEqual(err.count('ExpectationError'), 1, err)        # `true` can't close the block
        self.assertIn('root', out.splitlines()[-3])


class TestLatexShortcuts(unittest.TestCase):
    def test_only_whole_commands(self):
        # `\b` is the box of modal.kurt, but `\bot` was replaced by `□ot`
        self.assertEqual(kurt.replace_latex_syntax(r'\b A'), '□ A')
        self.assertEqual(kurt.replace_latex_syntax(r'\cap\cup'), '∩∪')
        for command in (r'\bot', r'\div', r'\bigcup'):
            self.assertEqual(kurt.replace_latex_syntax(command), command)


if __name__ == '__main__':
    unittest.main()
