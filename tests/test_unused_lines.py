import io
import os
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt

from tests.utils import PROJECT_ROOT

# the lines of a proof that nothing cites (todo 37, 2026-10-14): the editors grey them out, `kurt
# --unused` names them -- backwards from the top-level lines, the labelled ones and `qed`, along what
# each step cites; a block's result cites the block's conclusion and its first line


def unused(text: str) -> tuple[set[int], dict[int, str]]:
    result = kurt.check_text(text)
    assert result.ok, result.error
    return kurt.unused_lines(result.events)


LET = '''load logic
use (∀x P(x)) "h1"
use (∀x (P(x) ⇒ Q(x))) "h2"
use R(c)
show ∀x Q(x)
proof
    let x
        P(x)
        R(c)
        Q(x)
    ∀x Q(x)
qed
'''


class TestUnusedLines(unittest.TestCase):
    def test_a_step_that_nothing_cites(self):
        lines, restates = unused(LET)
        self.assertEqual(lines, {9})                                    # `R(c)`: no later line needs it
        self.assertIn('restates what the block 7-10 proves (forall-intro)', restates[11])   # not greyed (7: the `let` that opened the block)

    def test_a_block_whose_result_nothing_needs(self):
        # `qed` proves `R(c) ⇒ R(c)` without the blocks: they are not used, with their first lines
        text = LET + 'show R(c) ⇒ R(c)\nproof\n    assume R(c)\n        P(c)\n        Q(c)\n    assume P(c)\n        Q(c)\n    R(c)\nqed\n'
        lines, _ = unused(text)
        self.assertEqual(lines, {9, 15, 16, 17, 18, 19, 20})

    def test_a_block_of_one_line(self):
        # the result of a block of one line has that line's number, at the line after it
        lines, _ = unused('load logic, equality\nshow forall $x ($x = $x)\nproof\n    let x\n        x = x\nqed\n')
        self.assertEqual(lines, set())

    def test_nested_blocks_and_cases(self):
        text = ('load logic\nuse A or B\nuse A ⇒ C\nuse B ⇒ C\nuse E\nshow C\nproof\n    case A\n        C\n'
                '    case B\n        E\n        C\nqed\nshow D ⇒ (E ⇒ D)\nproof\n    assume D\n        assume E\n            D\nqed\n')
        lines, _ = unused(text)
        self.assertEqual(lines, {11})                                   # `E` in the second case

    def test_what_is_never_reported(self):
        # the top level; `expect` and `sandbox` blocks; restating an assumption; a proof's last line
        # that is its goal, also when `qed` proves the goal again without citing it
        text = ('load numbers, logic\nuse A\nA\nshow A\nproof\n    expect "ProofError"\n        B\n    A\nqed\n'
                'sandbox\n    use false\n    A\nuse ∃ $x P($x)\nuse P($x) ⇒ A\nshow A\nproof\n    pick c with P(c)\n'
                '        P(c)\n        A\nqed\ncalc on\nshow 2 + 3 = 5\nproof\n    2 + 3 = 5\nqed\n')
        lines, restates = unused(text)
        self.assertEqual(lines, set())
        self.assertIn('assumption', restates[18])

    def test_a_chain_line_that_restates_the_one_before(self):
        # tutorial 22: `≡ B ∨ ¬A` is `¬A ∨ B` (sym) -- the later lines cite the first
        path = PROJECT_ROOT / 'tutorial' / '22-prove-a-law-of-logic.kurt'
        result = kurt.Session(kurt.RunConfig()).check_file(str(path))
        lines, restates = kurt.unused_lines(result.events)
        self.assertNotIn(50, lines)
        self.assertIn('restates line 49', restates[50])

    def test_a_chain_whose_last_line_needs_none_of_the_others(self):
        # `A ⇔ C` is found by "ac" alone: the middle lines are not used, but the chain's first line
        # is -- the last line takes its left side `A` from there (mafi1/03-formulas.kurt, 2026-10-15)
        text = 'load propositional\nprop A, B, C, D\nuse A ⇔ B "ab"\nuse B ⇔ D "bd"\nuse A ⇔ C "ac"\nshow A ⇔ C\nproof\n    A ⇔ B\n      ⇔ D\n      ⇔ C\nqed\n'
        result = kurt.check_text(text)
        assert result.ok, result.error
        self.assertEqual([e.get('chain') for e in result.events if e.get('line') in (8, 9, 10) and e.get('kind') == 'step'][:3], [None, 8, 8])
        lines, _ = kurt.unused_lines(result.events)
        self.assertEqual(lines, {9})

    def test_the_editors_grey_it_out_and_the_hover_says_why(self):
        with tempfile.TemporaryDirectory() as tmp:
            uri = 'file://' + os.path.join(tmp, 'u.kurt')
            server = kurt.LanguageServer(io.BytesIO(), io.BytesIO())
            published = []
            server.publish_diagnostics = lambda uri, diagnostics, version: published.append(diagnostics)
            server.texts[uri], server.versions[uri] = LET, 1
            server.check(uri)
            hints = [d for d in published[-1] if d['severity'] == 4]
            self.assertEqual([(d['range']['start']['line'], d['tags']) for d in hints], [(8, [1])])   # (0-based)
            def hover(line):
                return server.hover({'textDocument': {'uri': uri}, 'position': {'line': line, 'character': 0}})['contents']['value']
            self.assertIn('**not used:**', hover(8))
            self.assertIn('**restates**', hover(10))
            self.assertNotIn('not used', hover(9))

    def test_the_command_line(self):
        env = dict(os.environ)
        env['PYTHONPATH'] = str(PROJECT_ROOT / 'src') + os.pathsep + env.get('PYTHONPATH', '')
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'u.kurt')
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(LET)
            result = subprocess.run([sys.executable, '-m', 'kurt.kurt', '--no-kurtc', '--unused', path],
                                    env=env, capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('Proof checked', result.stdout)
        self.assertTrue(result.stdout.rstrip().endswith('Not used: line 9 (no later line, block or `qed` cites them)'), result.stdout)

    def test_the_command_line_with_an_error(self):
        # it printed only the banner (2026-10-14, found by the docs hunt): the error goes to stderr
        env = dict(os.environ)
        env['PYTHONPATH'] = str(PROJECT_ROOT / 'src') + os.pathsep + env.get('PYTHONPATH', '')
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'bad.kurt')
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write('prop A\nA\n')
            result = subprocess.run([sys.executable, '-m', 'kurt.kurt', '--no-kurtc', '--unused', path],
                                    env=env, capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 1)
        self.assertIn('ProofError: can not derive `A`', result.stderr)


if __name__ == '__main__':
    unittest.main()
