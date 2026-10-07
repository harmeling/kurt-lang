import os
import subprocess
import sys
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# `kurt -v`, `kurt -V`, `kurt --version` show the version


class TestCliVersion(unittest.TestCase):
    def run_kurt(self, *args):
        env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
        return subprocess.run([sys.executable, '-m', 'kurt', *args], env=env, capture_output=True, text=True)

    def test_version(self):
        for flag in ('-v', '-V', '--version'):
            with self.subTest(flag=flag):
                run = self.run_kurt(flag)
                self.assertEqual(run.returncode, 0)
                self.assertEqual(run.stdout.strip(), f'kurt {kurt.version}')

    def test_no_verbose(self):
        # `--verbose` is gone: `cert N` shows the same, in full
        run = self.run_kurt('--verbose')
        self.assertEqual(run.returncode, 2)
        self.assertIn('unrecognized arguments: --verbose', run.stderr)

if __name__ == '__main__':
    unittest.main()
