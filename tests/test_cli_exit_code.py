import os
import sys
import subprocess
import tempfile
import unittest

from tests.utils import PROJECT_ROOT

def run_kurt(kurt_source: str) -> int:
    # invoke the real CLI entry point (`kurt.kurt:main`) in a subprocess, exactly the way a
    # script (CI, an autograder) would, so the exit code is genuinely observed rather than
    # inferred from in-process behaviour
    env = dict(os.environ)
    src_path = str(PROJECT_ROOT / "src")
    env["PYTHONPATH"] = src_path + os.pathsep + env.get("PYTHONPATH", "")
    with tempfile.NamedTemporaryFile(mode="w", suffix=".kurt", delete=False) as f:
        f.write(kurt_source)
        path = f.name
    try:
        result = subprocess.run(
            [sys.executable, "-m", "kurt.kurt", path],
            env=env, capture_output=True, text=True, timeout=30,
        )
        return result.returncode
    finally:
        os.unlink(path)

class TestCliExitCode(unittest.TestCase):
    def test_successful_proof_exits_zero(self):
        self.assertEqual(run_kurt("bool A\nuse A\nA\n"), 0)

    def test_failed_proof_exits_nonzero(self):
        # `A` is never `use`d, so this claim can't be derived -- a ProofError
        self.assertNotEqual(run_kurt("bool A\nA\n"), 0)

    def test_syntax_error_exits_nonzero(self):
        # `$$foo` can never lex as a symbol (see proofs/soundness/dollar-dollar-prefix-unparseable.kurt)
        self.assertNotEqual(run_kurt("var $$foo\n"), 0)

if __name__ == "__main__":
    unittest.main()
