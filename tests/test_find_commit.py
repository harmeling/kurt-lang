import hashlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from tests.utils import PROJECT_ROOT

SCRIPT = PROJECT_ROOT / "scripts" / "find_commit.py"


def git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@t", *args],
                          capture_output=True, text=True, check=True).stdout


class TestFindCommit(unittest.TestCase):
    """scripts/find_commit.py: the commit of a `kurt -v` fingerprint (the SHA-256 of the bytes of kurt.py)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.repo = Path(self.tmp.name)
        git(self.repo, "init", "-q")
        (self.repo / "src" / "kurt").mkdir(parents=True)
        self.versions = [b"version = '1'\n", b"version = '2'\n"]
        for n, text in enumerate(self.versions):
            (self.repo / "src" / "kurt" / "kurt.py").write_bytes(text)
            git(self.repo, "add", "-A")
            git(self.repo, "commit", "-q", "-m", f"release {n + 1}")
        (self.repo / "other.txt").write_text("a commit that does not touch kurt.py\n")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "other")

    def find(self, sha: str) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, str(SCRIPT), sha, "--repo", str(self.repo)], capture_output=True, text=True)

    def test_finds_the_commit_of_each_version(self):
        for n, text in enumerate(self.versions):
            done = self.find(hashlib.sha256(text).hexdigest()[:12])
            self.assertEqual(done.returncode, 0, done.stdout + done.stderr)
            self.assertIn(f"release {n + 1}", done.stdout)
            self.assertEqual(done.stdout.count("release"), 1)

    def test_a_prefix_and_upper_case_are_enough(self):
        done = self.find(hashlib.sha256(self.versions[0]).hexdigest()[:8].upper())
        self.assertEqual(done.returncode, 0)
        self.assertIn("release 1", done.stdout)

    def test_a_file_with_local_changes_matches_nothing(self):
        done = self.find(hashlib.sha256(b"version = '1 modified'\n").hexdigest()[:12])
        self.assertEqual(done.returncode, 1)
        self.assertIn("no commit has this kurt.py", done.stdout)

    def test_a_short_or_non_hex_argument_is_refused(self):
        self.assertNotEqual(self.find("abc").returncode, 0)
        self.assertNotEqual(self.find("zzzzzzzz").returncode, 0)


if __name__ == "__main__":
    unittest.main()
