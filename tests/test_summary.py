import unittest

import kurt.kurt as kurt

# `summary`: where the proof is -- the open blocks (a `case` as `case`), the claims still to
# prove, the latest facts, what could come next. It replaces `mode`, `level`, `context` and
# `trail` (2026-10-09).

PROOF = '''load prop
bool A, B, C
use A or B
use A implies C
use B implies C
show C
proof
    case A
        summary
        C
    case B
        C
qed
summary
'''


class TestSummary(unittest.TestCase):
    def test_inside_and_outside_blocks(self):
        result = kurt.check_text(PROOF)
        self.assertTrue(result.ok, result.error)
        first, second = result.output.split('; open: case A', 1)[1], result.output.rsplit('qed', 1)[1]
        self.assertIn('; open: proof', result.output)
        self.assertIn('; to prove: C', first)
        self.assertNotIn('; open:', second)                     # after `qed`, nothing is open
        self.assertIn('; fact:', second)

    def test_the_old_inspection_keywords_are_gone(self):
        for word in ('mode', 'level', 'context', 'trail'):
            self.assertNotIn(word, kurt.keywords)
        self.assertIn('summary', kurt.keywords)

    def test_no_trailing_space(self):
        # `; next, e.g.: implies ` (the step as Tab writes it, with its space; 2026-10-14)
        from tests.utils import PROJECT_ROOT
        out = kurt.Session(kurt.RunConfig()).check_file(str(PROJECT_ROOT / 'keywords' / '23-summary.kurt')).output
        nexts = [line for line in out.splitlines() if line.startswith('; next')]
        self.assertTrue(nexts, out)
        self.assertFalse([line for line in nexts if line != line.rstrip()], nexts)

if __name__ == '__main__':
    unittest.main()
