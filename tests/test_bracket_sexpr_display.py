import os
import sys
import subprocess
import tempfile
import unittest

from tests.utils import PROJECT_ROOT

def run_kurt(kurt_source: str) -> str:
    # `parse`'s output is only printed for the main file (see kurt.py's `printing`), which the
    # auto-discovered proofs/ test harness never exercises (it always calls `load_file` with `main=
    # False`). So this display bug needs a real CLI run, not a `.kurt` proof file, to catch it.
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
        return result.stdout
    finally:
        os.unlink(path)

class TestBracketSexprDisplay(unittest.TestCase):
    def test_custom_bracket_does_not_leak_placeholder(self):
        # a user-declared custom bracket pair is internally represented as a synthetic
        # combined token (e.g. `[$$$]`) so the parser can recognise the bracket-placeholder
        # node later. Displaying it should show `[]`, never the internal `$$$` marker.
        out = run_kurt('brackets "[" "]"\nbool A\nparse [A]\n')
        self.assertIn('([] A)', out)
        self.assertNotIn('$$$', out)

if __name__ == "__main__":
    unittest.main()
