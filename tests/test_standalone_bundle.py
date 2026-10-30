import importlib.util
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from tests.utils import PROJECT_ROOT

BUILD_SCRIPT = PROJECT_ROOT / "scripts" / "build_standalone.py"

def build_bundle(output_path):
    spec = importlib.util.spec_from_file_location("build_standalone", BUILD_SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.build(output_path)

class TestStandaloneBundle(unittest.TestCase):
    """Regression test for the generated single-file `kurt.py` (`scripts/build_standalone.py`):
    a download-just-this-one-file classroom workflow needs `load propositional` (etc.) to work with
    *no* `theories/` directory alongside it at all -- unlike the plain `src/kurt/kurt.py` +
    `theories/` copy covered by `test_standalone_script.py`, this file must be the only thing
    that exists."""

    @classmethod
    def setUpClass(cls):
        cls.bundle_dir = tempfile.mkdtemp()
        build_bundle(Path(cls.bundle_dir) / "kurt.py")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.bundle_dir, ignore_errors=True)

    def setUp(self):
        self.tmpdir = tempfile.mkdtemp()
        self.addCleanup(shutil.rmtree, self.tmpdir, ignore_errors=True)
        shutil.copy(Path(self.bundle_dir) / "kurt.py", Path(self.tmpdir) / "kurt.py")

    def run_bundle(self, kurt_source: str) -> subprocess.CompletedProcess:
        proof_path = os.path.join(self.tmpdir, "proof.kurt")
        with open(proof_path, "w") as f:
            f.write(kurt_source)
        env = dict(os.environ)
        env.pop("PYTHONPATH", None)   # must work with no PYTHONPATH at all
        return subprocess.run(
            [sys.executable, "kurt.py", "proof.kurt"],
            cwd=self.tmpdir, env=env, capture_output=True, text=True, timeout=30,
        )

    def test_bare_proof_without_load(self):
        result = self.run_bundle("prop A, B\nuse A implies B\nuse A\nB\n")
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertIn("Proof checked", result.stdout)

    def test_load_of_embedded_theory(self):
        # this is the whole point: `propositional.kurt` isn't on disk anywhere in `self.tmpdir`
        result = self.run_bundle("load propositional\nprop A, B\nuse A and B\nA\nB\n")
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertIn("Proof checked", result.stdout)

    def test_an_embedded_theory_is_checked_once(self):
        # (it had no hash, so it wasn't cached: checked again by each file that loads it, and
        # in each check of a session -- the playground took seconds for each change)
        script = (
            "import collections, kurt\n"
            "starts = collections.Counter()\n"
            "session = kurt.Session(kurt.RunConfig(progress=lambda e: e['line'] == 0 and starts.update([e['file']])))\n"
            "for _ in range(2):\n"
            "    assert session.check_text('load set\\nload propositional\\n').ok\n"
            "print(sorted(starts.items()))\n")
        env = dict(os.environ)
        env.pop("PYTHONPATH", None)
        result = subprocess.run([sys.executable, "-c", script], cwd=self.tmpdir, env=env,
                                capture_output=True, text=True, timeout=60)
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        starts = dict(eval(result.stdout))
        self.assertEqual(starts.pop('proof.kurt'), 2)
        self.assertIn('<embedded>/propositional.kurt', starts)       # (loaded by set.kurt too)
        self.assertEqual(set(starts.values()), {1}, starts)

    def test_the_certificates_of_the_theories_are_embedded(self):
        # the bundle can't write certificates next to its theories: without the embedded ones,
        # `load divisibility` took 8 s every time (and `load field` 15 s), instead of about 1 s
        script = (
            "import kurt\n"
            "session = kurt.new_session(kurt.RunConfig(kurtc=True))\n"
            "assert session.check_text('load divisibility\\n').ok\n"
            "print(session._state.replayed)\n")
        env = dict(os.environ, XDG_CACHE_HOME=os.path.join(self.tmpdir, "cache"))
        env.pop("PYTHONPATH", None)
        result = subprocess.run([sys.executable, "-c", script], cwd=self.tmpdir, env=env,
                                capture_output=True, text=True, timeout=120)
        self.assertEqual(result.returncode, 0, msg=result.stderr)
        self.assertGreater(int(result.stdout), 300)     # (the parts of an `assume A ∧ B` are not replayed since 2026-10-23: "and-elim" first, todo 50)
        self.assertFalse(os.path.exists(os.path.join(self.tmpdir, "cache")))   # (nothing to write)

    def test_no_directory_named_theories_exists(self):
        self.assertFalse(os.path.exists(os.path.join(self.tmpdir, "theories")))

if __name__ == "__main__":
    unittest.main()
