import unittest

import kurt


# cases the mutation fuzzer of the bug hunt of 2026-10-30 (dev/bug-hunt-2026-10-30/fuzz.py) found: a file may be
# rejected, but checking it must never end in a Python exception (an `AssertionError` of Kurt's own "BUG:" checks)

LAYOUT_OUT_OF_STEP = '''load logic, equality
use P c
show A ⇒ P c
proof
    assume A
        P c
show ∀ x (P x ⇒ P x)
proof
        assume P x
            P x
show A ⇒ ∃ y P y
proof
    assume A
        ∃ y P y
pick ('''


class TestFuzzFindings(unittest.TestCase):
    def test_a_statement_that_needs_more_input_after_a_dedent(self):
        # the cause of the "layout out of step" of the fuzzer (dev/bug-hunt-2026-10-30/layout-out-of-step.kurt): `pick` parses its
        # tail while it is evaluated, after the dedent of its line closed the blocks; an unclosed bracket then asked for the next
        # line, and the line was read again against the blocks that were closed already (before: "the indentation of line N
        # closes more blocks than are open", and "BUG: we should be one-level up" at the end of the file)
        for all_errors in (False, True):
            with self.subTest(all_errors=all_errors):
                session = kurt.Session(kurt.RunConfig(all_errors=all_errors))
                result = kurt.check_text(LAYOUT_OUT_OF_STEP, name='fuzz.kurt', session=session)
                self.assertFalse(result.ok)
                self.assertEqual(len(result.errors), 1, result.errors)           # the end of the file, nothing else
                self.assertIn('unexpected end of file while still parsing the statement', result.error or '')
        text = ('load logic, equality\nuse P c\nuse ∃ y (P y ∧ y = c)\nshow A ⇒ A\nproof\n    assume A\n        A\n'
                'pick y with (P y ∧\n        y = c)\n    P c\n')
        result = kurt.check_text(text, name='fuzz.kurt', session=kurt.Session())
        self.assertTrue(result.ok, result.error)

    def test_load_without_a_space_is_an_error(self):
        for text in ('load-a\n', 'load(a)\n', 'load ,\n'):
            with self.subTest(text=text):
                result = kurt.check_text(text, name='fuzz.kurt', session=kurt.Session())
                self.assertFalse(result.ok)


if __name__ == '__main__':
    unittest.main()
