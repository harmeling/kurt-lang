import os
import shutil
import subprocess
import sys
import tempfile
import unittest

from tests.utils import PROJECT_ROOT

class TestStandaloneScript(unittest.TestCase):
    """Regression test for the README/CLAUDE.md-advertised classroom workflow: copy just
    `src/kurt/kurt.py` (plus `theories/`) somewhere and run it directly with `python3
    kurt.py file.kurt`, with no install and no PYTHONPATH -- `kurt` is not an importable
    package in that scenario, so `theory_path`'s original unconditional `resources.files
    ("kurt.theories")` crashed with `ModuleNotFoundError: No module named 'kurt.theories';
    'kurt' is not a package` before the file being checked was even opened. See
    doc/kurt-soundness.md for the writeup."""

    def setUp(self):
        self.tmpdir = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.tmpdir, ignore_errors=True)
        shutil.copy(PROJECT_ROOT / "src" / "kurt" / "kurt.py", self.tmpdir)
        shutil.copytree(PROJECT_ROOT / "src" / "kurt" / "theories", os.path.join(self.tmpdir, "theories"))

    def run_standalone(self, kurt_source: str) -> subprocess.CompletedProcess:
        proof_path = os.path.join(self.tmpdir, "proof.kurt")
        with open(proof_path, "w") as f:
            f.write(kurt_source)
        env = dict(os.environ)
        env.pop("PYTHONPATH", None)   # must work with no PYTHONPATH at all -- that's the point
        return subprocess.run(
            [sys.executable, "kurt.py", "proof.kurt"],
            cwd=self.tmpdir, env=env, capture_output=True, text=True, timeout=30,
        )

    def test_bare_proof_without_load(self):
        result = self.run_standalone("bool A, B\nuse A implies B\nuse A\nB\n")
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertIn("Proof checked", result.stdout)

    def test_load_of_packaged_theory(self):
        result = self.run_standalone("load prop\nbool A, B\nuse A and B\nA\nB\n")
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertIn("Proof checked", result.stdout)

if __name__ == "__main__":
    unittest.main()
