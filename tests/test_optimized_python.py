import os
import subprocess
import sys
import unittest

from tests.utils import PROJECT_ROOT

# `python -O` removes the `assert`s, and with them internal soundness checks: Kurt refuses to
# check there, on the command line and from Python code (dev/astra-suggestions.md, finding 8)


class TestOptimizedPython(unittest.TestCase):
    def run_optimized(self, *args):
        env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
        return subprocess.run([sys.executable, '-O', *args], env=env, capture_output=True, text=True,
                              cwd=str(PROJECT_ROOT))

    def test_the_command_line(self):
        run = self.run_optimized('-m', 'kurt', 'tutorial/01-apply-an-implication-modus-ponens.kurt')
        self.assertEqual(run.returncode, 1)
        self.assertIn('python -O', run.stderr)

    def test_the_api(self):
        for call in ('kurt.check_text("true\\n")', 'kurt.new_session().check_text("true\\n")',
                     'kurt.Shell().start_text("true\\n")', 'kurt.check_file("tutorial/01-apply-an-implication-modus-ponens.kurt")',
                     'kurt.load_file("prop", copy.deepcopy(kurt.initial_kb))'):
            with self.subTest(call=call):
                run = self.run_optimized('-c', f'import copy, kurt.kurt as kurt; {call}; print("checked")')
                self.assertNotIn('checked', run.stdout)
                self.assertIn('python -O', run.stderr)
        # without -O, the same call checks
        env = dict(os.environ, PYTHONPATH=str(PROJECT_ROOT / 'src'))
        run = subprocess.run([sys.executable, '-c', 'import kurt; print(kurt.check_text("true\\n").ok)'],
                             env=env, capture_output=True, text=True)
        self.assertEqual(run.stdout.strip(), 'True')

if __name__ == '__main__':
    unittest.main()
