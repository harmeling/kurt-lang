import copy
import contextlib
import io
import unittest

import kurt.kurt as kurt


def shell(lines: list[str]):
    # the state of the shell after `lines`: (kb, lexer_state)
    kb = copy.deepcopy(kurt.initial_kb)
    state = kurt.LexerState()
    with contextlib.redirect_stdout(io.StringIO()):
        for n, text in enumerate(lines, 1):
            with kurt.quietly():
                kb, state = kurt.scan_parse_check_eval(text, state, kb, n, '<test>')
    return kb, state


class TestTab(unittest.TestCase):
    # what Tab offers in the shell (`completions`), without a terminal

    def test_the_value_after_an_equal_sign(self):
        kb, state = shell(['load numbers', 'calc on'])
        self.assertEqual(kurt.completions('17*42=', '', kb, state), ['714'])
        self.assertEqual(kurt.completions('1/3 + 1/6 =', '', kb, state), ['0.5'])
        self.assertEqual(kurt.completions('x + 1 =', '', kb, state), [])          # no value
        kb, state = shell(['load numbers'])
        self.assertEqual(kurt.completions('17*42=', '', kb, state), [])           # only with `calc on`

    def test_latex_shortcuts(self):
        kb, state = shell([])
        self.assertEqual(kurt.completions('show \\forall', '\\forall', kb, state), ['∀'])
        self.assertEqual(kurt.completions('M \\leadsto', '\\leadsto', kb, state), ['⇝'])
        self.assertIn('\\forall', kurt.completions('\\fo', '\\fo', kb, state))

    def test_theories_after_load(self):
        kb, state = shell([])
        self.assertEqual(kurt.completions('load nu', 'nu', kb, state), ['numbers'])
        self.assertIn('vectorspace', kurt.completions('load v', 'v', kb, state))
        self.assertNotIn('minimal', kurt.completions('load m', 'm', kb, state))

    def test_names_and_labels(self):
        kb, state = shell(['load prop', 'bool Apple'])
        self.assertIn('assume', kurt.completions('ass', 'ass', kb, state))
        self.assertIn('Apple', kurt.completions('Ap', 'Ap', kb, state))
        self.assertIn('and-elim', kurt.completions('and-e', 'and-e', kb, state))
        self.assertIn('"and-elim"', kurt.completions('cert "and-e', '"and-e', kb, state))

    def test_the_next_step(self):
        kb, state = shell(['load prop', 'bool A, B', 'use A', 'show A or B'])
        self.assertEqual(kurt.completions('', '', kb, state), ['proof'])
        kb, state = shell(['load prop', 'bool A, B', 'use A', 'show A or B', 'proof'])
        self.assertEqual(kurt.completions('    ', '', kb, state), ['A or B'])
        kb, state = shell(['load prop', 'bool A, B', 'use A', 'show A or B', 'proof', '    A or B'])
        self.assertEqual(kurt.completions('    ', '', kb, state), ['qed'])

    def test_the_next_case(self):
        kb, state = shell(['load prop', 'bool A, B, C', 'use A or B', 'use A implies C', 'use B implies C',
                           'case A', '    C'])
        self.assertEqual(kurt.completions('    ', '', kb, state), ['case B'])          # (to write dedented)
        kb, state = shell(['load prop', 'bool A, B, C', 'use A or B', 'use A implies C', 'use B implies C',
                           'case A', '    C', 'case B', '    C'])
        self.assertEqual(kurt.completions('    ', '', kb, state), ['C'])               # all cases: the goal


if __name__ == '__main__':
    unittest.main()


class TestHint(unittest.TestCase):
    def test_hint_on_shows_the_next_step_before_each_prompt(self):
        import subprocess, sys
        from tests.utils import PROJECT_ROOT
        text = 'load prop\nbool A, B\nuse A\nhint on\nshow A or B\nproof\n    A or B\nqed\n'
        out = subprocess.run([sys.executable, str(PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py'), '--no-kurtc'],
                             input=text, capture_output=True, text=True, cwd=PROJECT_ROOT).stdout
        hints = [line for line in out.splitlines() if line.startswith('; hint:')]
        self.assertEqual(hints, ['; hint: next, e.g. proof  (Tab writes it)',
                                 '; hint: next, e.g. A or B  (Tab writes it)',
                                 '; hint: next, e.g. qed  (Tab writes it)'])
