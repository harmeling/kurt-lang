import contextlib
import re
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
        old = kurt.run_state.kurtc_enabled
        kurt.run_state.kurtc_enabled = False
        try:
            with contextlib.redirect_stdout(out):
                kurt.load_file(path, copy.deepcopy(kurt.initial_kb), main=True)
        finally:
            kurt.run_state.kurtc_enabled = old
    lines = {}
    for line in out.getvalue().splitlines():
        if ';' in line:
            claim, reason = line.split(';', 1)
            number = re.match(r'\s*(\d+)  ', claim)      # (the number of the line, in front)
            claim = claim[number.end():] if number else claim
            lines[claim.strip()] = f'{number.group(1)} {reason.strip()}' if number else reason.strip()
    return lines


class TestReasons(unittest.TestCase):
    def test_reflexivity_is_equal_intro(self):
        # it was "by chain-trans-0-0(pow-identity, pow-identity)" with number.kurt, and
        # "by equal-elim(equal-intro, equal-intro)" with equality.kurt
        for theory in ('equality', 'number'):
            with self.subTest(theory=theory):
                self.assertEqual(reasons(f'load {theory}\nconst a\na = a\n')['a = a'], '3 by equal-intro')

    def test_a_conjunction_is_and_intro(self):
        # it was "by equal-elim(5, 7, 7)", then "by iff-reflexive(7, 7)"
        r = reasons('load number\nprop A\nuse A\nA and A\n')
        self.assertEqual(r['A and A'], '4 by and-intro(3, 3)')

    def test_qed_cites_its_proof(self):
        # `qed` tries the proof's own last line first: it was "by chain-trans-1-1(iff-elim-backward,
        # top-elim)" for the proof of "iff-true-elim" in propositional.kurt, whose lines then
        # counted as unused (2026-10-20)
        r = reasons('load propositional\nshow (%A iff true) implies %A\nproof\n    assume %A iff true\n'
                    '        true implies %A\n        %A\nqed\n')
        self.assertEqual(r['qed'], '7 by 4-6')

    def test_modus_ponens(self):
        r = reasons('load propositional\nprop A, B\nuse A implies B\nuse A\nB\n')
        self.assertEqual(r['B'], '5 by 3(4)')


    def test_a_closed_sandbox_by_its_lines(self):
        # numbered by the line after it -- at the end of a file of 4 lines: "5 closed" (2026-10-14)
        out = kurt.check_text('load propositional\nprop A\nsandbox\n    use A\n    A\n').output
        self.assertIn('; 3-5 closed, its content is discarded', out)   # (from the `sandbox` line that opened it, like any block; 2026-10-15)


if __name__ == '__main__':
    unittest.main()
