import contextlib
import copy
import io
import os
import tempfile
import unittest

import kurt.kurt as kurt

# the reason Kurt prints for a step names the rule a student expects: the search tries facts
# first, then rules with a specific conclusion, then a conjunction clause by clause, and only then
# the rules whose conclusion fits almost anything ("equal-elim", "bottom-elim", "iff-reflexive")


def reasons(text: str) -> dict[str, str]:
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'f.kurt')
        with open(path, 'w') as fh:
            fh.write(text)
        out = io.StringIO()
        old = kurt.kurtc_enabled
        kurt.kurtc_enabled = False
        try:
            with contextlib.redirect_stdout(out):
                kurt.load_file(path, copy.deepcopy(kurt.initial_kb), mainstream=True)
        finally:
            kurt.kurtc_enabled = old
    lines = {}
    for line in out.getvalue().splitlines():
        if ';' in line:
            claim, reason = line.split(';', 1)
            lines[claim.strip()] = reason.strip()
    return lines


class TestReasons(unittest.TestCase):
    def test_reflexivity_is_equal_intro(self):
        # it was "by chain-trans-0-0(pow-identity, pow-identity)" with numbers.kurt, and
        # "by equal-elim(equal-intro, equal-intro)" with equality.kurt
        for theory in ('equality', 'numbers'):
            with self.subTest(theory=theory):
                self.assertEqual(reasons(f'load {theory}\nconst a\na = a\n')['a = a'], '3 by equal-intro')

    def test_a_conjunction_is_and_intro(self):
        # it was "by equal-elim(5, 7, 7)", then "by iff-reflexive(7, 7)"
        r = reasons('load numbers\nbool A\nuse A\nA and A\n')
        self.assertEqual(r['A and A'], '4 by and-intro(3, 3)')

    def test_modus_ponens(self):
        r = reasons('load prop\nbool A, B\nuse A implies B\nuse A\nB\n')
        self.assertEqual(r['B'], '5 by 3(4)')


if __name__ == '__main__':
    unittest.main()
