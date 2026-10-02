import os
import shutil
import subprocess
import sys
import tempfile
import unittest

from tests.utils import PROJECT_ROOT

# scripts/kurt2lean.py writes a checked Kurt proof as a Lean 4 file; where Lean is installed
# (`lean` on the PATH, or ~/.elan/bin/lean), Lean checks it again -- otherwise only the
# translation itself is tested

SCRIPT = PROJECT_ROOT / 'scripts' / 'kurt2lean.py'
LEAN = shutil.which('lean') or next((p for p in [os.path.expanduser('~/.elan/bin/lean')] if os.path.isfile(p)), None)
PROOFS = ['proofs/readme/contrapositive.kurt', 'proofs/natural-deduction/neg-forall.kurt',
          'proofs/natural-deduction/lemma.kurt']


def translate(proof: str, output: str) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(SCRIPT), str(PROJECT_ROOT / proof), '-o', output, '--strict-lean'],
                          capture_output=True, text=True, timeout=120)


def lean(path: str) -> subprocess.CompletedProcess:
    return subprocess.run([LEAN, os.path.basename(path)], cwd=os.path.dirname(path), capture_output=True, text=True, timeout=300)


class TestKurt2Lean(unittest.TestCase):
    def test_translates_completely(self):
        with tempfile.TemporaryDirectory() as tmp:
            for proof in PROOFS:
                with self.subTest(proof=proof):
                    out = os.path.join(tmp, 'proof.lean')
                    result = translate(proof, out)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    text = open(out, encoding='utf-8').read()
                    self.assertIn('theorem ', text)
                    self.assertNotIn('sorry', text)

    @unittest.skipUnless(LEAN, 'Lean is not installed')
    def test_lean_checks_the_translation(self):
        with tempfile.TemporaryDirectory() as tmp:
            for proof in PROOFS:
                with self.subTest(proof=proof):
                    out = os.path.join(tmp, 'proof.lean')
                    translate(proof, out)
                    result = lean(out)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertNotIn('error', result.stdout)

    @unittest.skipUnless(LEAN, 'Lean is not installed')
    def test_lean_rejects_a_false_theorem(self):
        # the translation checks something: with the theorem changed into a false one (the
        # converse of the contrapositive), Lean fails
        with tempfile.TemporaryDirectory() as tmp:
            out = os.path.join(tmp, 'proof.lean')
            translate('proofs/readme/contrapositive.kurt', out)
            text = open(out, encoding='utf-8').read()
            true, false = '((A → B) → ((¬ B) → (¬ A)))', '((A → B) → ((¬ A) → (¬ B)))'
            self.assertIn(f'theorem f', text)
            self.assertIn(true, text)
            with open(out, 'w', encoding='utf-8') as fh:
                fh.write(text.replace(true, false, 1))
            result = lean(out)
            self.assertNotEqual(result.returncode, 0)


if __name__ == '__main__':
    unittest.main()
