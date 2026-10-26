import re
import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# analysis.kurt states the laws of subtraction and halving as axioms (their proofs would make it
# slow to check); proofs/arithmetic/helpers/subtraction.kurt derives them from "sub-def" -- checked
# here against a copy of analysis.kurt without them, so that no proof can cite its own law

LAWS = ('sub-add-cancel', 'sub-zero', 'sub-split', 'sub-add', 'sub-mul', 'double', 'halves', 'le-mul-nonneg')
THEORY = PROJECT_ROOT / 'src' / 'kurt' / 'theories' / 'analysis.kurt'
PROOFS = PROJECT_ROOT / 'proofs' / 'arithmetic' / 'helpers' / 'subtraction.kurt'


class TestSubtractionLaws(unittest.TestCase):
    def test_the_laws_follow_from_sub_def(self):
        theory = THEORY.read_text(encoding='utf-8')
        laws = [line for line in theory.splitlines()
                if line.startswith('use ') and (label := re.search(r'"([a-z-]+)"\s*$', line))
                and label.group(1) in LAWS]
        self.assertEqual(len(laws), len(LAWS))
        self.assertIn('"sub-def"', theory)
        # (and their proofs in Lean, `lean "sub-zero" ...`, which need the facts)
        proofs_in_lean = [line for line in theory.splitlines()
                          if (m := re.match(r'lean "([a-z-]+)" ', line)) and m.group(1) in LAWS]
        self.assertTrue(proofs_in_lean)
        without = '\n'.join(line for line in theory.splitlines() if line not in laws and line not in proofs_in_lean) + '\n'
        proofs = PROOFS.read_text(encoding='utf-8')
        self.assertEqual(proofs.count('\nshow '), len(LAWS))
        with tempfile.TemporaryDirectory() as tmp:
            (Path(tmp) / 'analysis-without.kurt').write_text(without, encoding='utf-8')
            checked = Path(tmp) / 'subtraction.kurt'
            checked.write_text(proofs.replace('load analysis\n', 'load analysis-without\n'), encoding='utf-8')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))   # trusted, like analysis.kurt
            result = kurt.check_file(str(checked), session=session)
        self.assertTrue(result.complete, result.error)
        for law in LAWS:
            self.assertNotIn(f'by {law}', result.output)


if __name__ == '__main__':
    unittest.main()
