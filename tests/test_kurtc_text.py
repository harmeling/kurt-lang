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

    def test_the_options_hold_for_a_kurtc_too(self):
        # `kurt --strict p.kurtc` checks p.kurt as `kurt --strict p.kurt` does (dev/astra-suggestions.md, 3)
        env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
        def run(*args):
            return subprocess.run([sys.executable, '-m', 'kurt', *args], env=env, capture_output=True, text=True)
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as teacher:
            bad = os.path.join(tmp, 'bad.kurt')
            with open(bad, 'w', encoding='utf-8') as f:
                f.write('use false\nfalse\n')
            self.assertEqual(run('--strict', bad).returncode, 1)
            self.assertEqual(run('--strict', bad + 'c').returncode, 1)
            self.assertEqual(run(bad + 'c').returncode, 0)
            # `-p`: a theory found there, also for the `.kurtc`
            with open(os.path.join(teacher, 'axioms.kurt'), 'w', encoding='utf-8') as f:
                f.write('bool C\nuse C "c"\n')
            good = os.path.join(tmp, 'good.kurt')
            with open(good, 'w', encoding='utf-8') as f:
                f.write('load axioms\nC\n')
            self.assertEqual(run('--strict', '-p', teacher, good).returncode, 0)
            self.assertEqual(run('--strict', '-p', teacher, good + 'c').returncode, 0)
            self.assertEqual(run('--json', good + 'c').returncode, 1)    # --json is for the `.kurt`

if __name__ == '__main__':
    unittest.main()
