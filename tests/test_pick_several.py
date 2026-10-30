import builtins
import contextlib
import copy
import io
import unittest

import kurt.kurt as kurt

# `pick x, y, z with F` (several witnesses at once): the blocks nested, the lines indent once -- in the interactive shell (typed or
# pasted) and in the language server's check (todo 85)

TEXT = '''load logic, number
use ∃ x ∃ y (x < y) "two"
use ∃ x ∃ y ∃ z (x < y ∧ y < z) "three"
show ∃ a ∃ b (a < b)
proof
    pick x, y, z with x < y ∧ y < z
        x < y
        ∃ a ∃ b (a < b)
qed
'''


def shell(lines):
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


class TestPickSeveral(unittest.TestCase):
    def test_the_file(self):
        result = kurt.Session().check_text(TEXT)
        self.assertTrue(result.ok, result.error)

    def test_the_shell_takes_it_pasted(self):
        out, err = shell(TEXT.splitlines())
        self.assertEqual(err, '')
        self.assertIn('exists-elim', out)

    def test_the_shell_goes_on_after_the_dedent(self):
        out, err = shell(TEXT.splitlines() + ['show ∃ u ∃ v (u < v)', 'proof', '    pick x, y, z with x < y ∧ y < z', '        x < y', '        ∃ u ∃ v (u < v)', 'qed'])
        self.assertEqual(err, '')

    def test_the_server_checks_it_with_all_errors(self):
        # (the same text through a check of the server's kind: a file with an error after it is still reported once)
        result = kurt.Session(kurt.RunConfig(all_errors=True)).check_text(TEXT + 'show ∃ p (p < p)\nproof\n    pick x with x < x\n        x < x\nqed\n')
        self.assertFalse(result.ok)
        self.assertTrue(all(e["line"] >= 10 for e in result.errors), result.errors)        # (only the bad block, after the good one)

    def test_break_gives_up_all_the_blocks_of_the_pick(self):
        # (before 2026-10-30 only the innermost was discarded, and the next dedent failed: "may not contain constant symbols")
        result = kurt.Session().check_text(TEXT.split('show')[0] + 'show ∃ a ∃ b (a < b)\nproof\n    pick x, y with x < y\n        break\n    ∃ a ∃ b (a < b)\nqed\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('discarded the 2 blocks of the `pick`', result.output)
