import os
import subprocess
import sys
import tempfile
import unittest

from tests.utils import PROJECT_ROOT


class TestTrustThroughLinks(unittest.TestCase):
    def test_a_theory_of_kurt_named_by_its_real_path_is_trusted(self):
        # Kurt imported through a symbolic link, the theory opened by its real path (an editor names
        # the real path): one file under two spellings. Before 2026-10-20 the paths were compared as
        # strings, the theory counted as a file of the user's, and its roles were refused
        # ("the role `equivalence` ... can only be given by a theory that comes with Kurt")
        with tempfile.TemporaryDirectory() as tmp:
            link = os.path.join(tmp, 'linked-src')
            os.symlink(PROJECT_ROOT / 'src', link)
            real = PROJECT_ROOT / 'src' / 'kurt' / 'theories' / 'propositional.kurt'
            env = {**os.environ, 'PYTHONPATH': link}
            result = subprocess.run([sys.executable, '-m', 'kurt', '-a', '--no-kurtc', str(real)],
                                    capture_output=True, text=True, timeout=300, env=env, cwd=tmp)
            self.assertEqual(result.returncode, 0, result.stdout[-1500:] + result.stderr[-1500:])
            self.assertIn('Proof checked', result.stdout)


if __name__ == '__main__':
    unittest.main()
