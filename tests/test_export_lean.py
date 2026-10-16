import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

from tests.utils import PROJECT_ROOT

# `kurt --lean FILE` (`export_lean`, before 2026-10-13 scripts/kurt2lean.py) writes a checked Kurt
# proof as a Lean 4 file; where Lean is installed (`lean` on the PATH, or ~/.elan/bin/lean), Lean
# checks it again -- otherwise only the translation itself is tested. The translation is tested with
# the Lean of scripts/lean-toolchain (the CI job `lean` installs it); an older Lean is skipped, since
# it may not know an option or a tactic the translation uses. KURT_REQUIRE_LEAN=1 (in CI): no Lean,
# or an older one, is an error.

KURT = PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py'
LEAN = shutil.which('lean') or next((p for p in [os.path.expanduser('~/.elan/bin/lean')] if os.path.isfile(p)), None)
TOOLCHAIN = (PROJECT_ROOT / 'scripts' / 'lean-toolchain').read_text(encoding='utf-8').strip()
TESTED = tuple(int(n) for n in re.search(r'v(\d+)\.(\d+)', TOOLCHAIN).groups())


def lean_version(lean_path):
    # (major, minor) of the Lean at `lean_path`, or None
    try:
        out = subprocess.run([lean_path, '--version'], capture_output=True, text=True, timeout=60).stdout
    except OSError:
        return None
    found = re.search(r'version (\d+)\.(\d+)', out)
    return tuple(int(n) for n in found.groups()) if found else None


VERSION = lean_version(LEAN) if LEAN else None
USABLE = VERSION is not None and VERSION >= TESTED
WHY_NOT = ('Lean is not installed' if not LEAN else
           f'Lean {VERSION} is older than {TOOLCHAIN} (scripts/lean-toolchain)')
PROOFS = ['proofs/readme/contrapositive.kurt', 'proofs/natural-deduction/neg-forall.kurt',
          'proofs/natural-deduction/lemma.kurt']


def translate(proof: str, tmp: str) -> tuple[subprocess.CompletedProcess, str]:
    # `kurt --lean` on a copy of the proof in `tmp` (it writes the `.lean` next to the file)
    copy = os.path.join(tmp, 'proof.kurt')
    shutil.copy(PROJECT_ROOT / proof, copy)
    result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', copy], capture_output=True, text=True, timeout=120)
    return result, os.path.join(tmp, 'proof.lean')


def lean(path: str) -> subprocess.CompletedProcess:
    return subprocess.run([LEAN, os.path.basename(path)], cwd=os.path.dirname(path), capture_output=True, text=True, timeout=300)


class TestExportLean(unittest.TestCase):
    def test_lean_is_there_where_required(self):
        if os.environ.get('KURT_REQUIRE_LEAN'):
            self.assertTrue(USABLE, WHY_NOT)

    def test_translates_completely(self):
        for proof in PROOFS:
            with self.subTest(proof=proof), tempfile.TemporaryDirectory() as tmp:
                result, out = translate(proof, tmp)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('wrote', result.stdout)
                self.assertEqual(result.stdout.strip().splitlines()[-1], f'lean {out}')   # the command, last
                text = open(out, encoding='utf-8').read()
                self.assertIn('theorem ', text)
                self.assertNotIn('sorry', text)

    @unittest.skipUnless(USABLE, WHY_NOT)
    def test_lean_checks_the_translation(self):
        for proof in PROOFS:
            with self.subTest(proof=proof), tempfile.TemporaryDirectory() as tmp:
                _, out = translate(proof, tmp)
                result = lean(out)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn('error', result.stdout)

    @unittest.skipUnless(USABLE, WHY_NOT)
    def test_lean_rejects_a_false_theorem(self):
        # the translation checks something: with the theorem changed into a false one (the
        # converse of the contrapositive), Lean fails -- at the theorem, for its type, while the
        # same file with the true theorem passes (so the failure isn't an option Lean doesn't know)
        with tempfile.TemporaryDirectory() as tmp:
            _, out = translate('proofs/readme/contrapositive.kurt', tmp)
            text = open(out, encoding='utf-8').read()
            true, false = '((A → B) → ((¬ B) → (¬ A)))', '((A → B) → ((¬ A) → (¬ B)))'
            self.assertIn('theorem f', text)
            self.assertIn(true, text)
            control = lean(out)
            self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
            with open(out, 'w', encoding='utf-8') as fh:
                fh.write(text.replace(true, false, 1))
            result = lean(out)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('Type mismatch', result.stdout + result.stderr)
            self.assertIn('¬A → ¬B', result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
