import os
import subprocess
import sys
import tempfile
import unittest

from tests.utils import PROJECT_ROOT

# `kurt foo.kurtc`: the certificates of foo.kurt, readable, line by line


class TestKurtcText(unittest.TestCase):
    def test_text(self):
        env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'p.kurt')
            with open(path, 'w', encoding='utf-8') as f:
                f.write('load numbers\nconst a, b\nuse a = b\na + 1 = b + 1\nassume a = 0\n    0 = a\nb = a\n')
            subprocess.run([sys.executable, '-m', 'kurt', path], env=env, capture_output=True, check=True)
            run = subprocess.run([sys.executable, '-m', 'kurt', path + 'c'], env=env, capture_output=True, text=True)
            self.assertEqual(run.returncode, 0)
            out = run.stdout
            self.assertIn('(certified', out)
            self.assertIn('line 4: a + 1 = b + 1', out)
            self.assertIn('"add-eq"', out)
            self.assertIn('premise:   `a = b` (line 3)', out)
            self.assertIn('"impl-intro", closing the block `assume', out)
            with open(path, 'a', encoding='utf-8') as f:
                f.write('; changed\n')
            out = subprocess.run([sys.executable, '-m', 'kurt', path + 'c'], env=env, capture_output=True, text=True).stdout
            self.assertIn('out of date', out)
            missing = subprocess.run([sys.executable, '-m', 'kurt', os.path.join(tmp, 'q.kurtc')], env=env, capture_output=True, text=True)
            self.assertEqual(missing.returncode, 1)

if __name__ == '__main__':
    unittest.main()
