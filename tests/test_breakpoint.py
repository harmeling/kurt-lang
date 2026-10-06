import os
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

PROOF = 'load prop\nbool A, B\nuse A\nuse A implies B\nshow A and B\nproof\n    B\n    breakpoint\n    A and B\nqed\n'


def run(files: dict[str, str], args: list[str], stdin: str = '') -> subprocess.CompletedProcess:
    with tempfile.TemporaryDirectory() as tmp:
        for name, text in files.items():
            with open(os.path.join(tmp, name), 'w') as fh:
                fh.write(text)
        return subprocess.run([sys.executable, str(PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py'), '--no-kurtc', *args],
                              input=stdin, capture_output=True, text=True, cwd=tmp)


class TestBreakpoint(unittest.TestCase):
    def test_without_a_shell_it_shows_the_state_and_goes_on(self):
        done = run({'p.kurt': PROOF}, ['p.kurt'])
        self.assertEqual(done.returncode, 0)
        self.assertIn('breakpoint                            ; 8 the state here', done.stdout)
        self.assertIn('; to prove: A and B', done.stdout)
        self.assertIn('; next, e.g.: A and B', done.stdout)
        self.assertIn('Proof checked', done.stdout)

    def test_with_i_the_shell_continues_there(self):
        # the rest of the proof is typed in the shell, inside the open `proof` block
        done = run({'p.kurt': PROOF.replace('    A and B\nqed\n', '')}, ['-i', 'p.kurt'], '    A and B\nqed\n')
        self.assertIn('; breakpoint at line 8: the shell continues here', done.stdout)
        self.assertIn('9 by and-intro', done.stdout)
        self.assertIn('10 by 9', done.stdout)

    def test_kurt_i_continues_at_the_failing_line(self):
        failing = PROOF.replace('    breakpoint\n    A and B\n', '    A and C\n')
        done = run({'p.kurt': failing}, ['-i', 'p.kurt'], '    A and B\nqed\n')
        self.assertIn('can not derive', done.stderr)
        self.assertIn('; the shell continues at line 8, with the state there', done.stdout)
        self.assertIn('8 by and-intro', done.stdout)
        self.assertEqual(done.returncode, 1)          # the file itself failed

    def test_in_a_loaded_file_it_is_skipped(self):
        lib = 'load prop\nbool A\nuse A "a"\nbreakpoint\n'
        done = run({'lib.kurt': lib, 'main.kurt': 'load lib\nA\n'}, ['main.kurt'])
        self.assertEqual(done.returncode, 0)
        self.assertNotIn('the state here', done.stdout)

    def test_from_python_it_shows_the_state(self):
        result = kurt.check_text(PROOF)
        self.assertTrue(result.complete)
        self.assertIn('; to prove: A and B', result.output)


if __name__ == '__main__':
    unittest.main()
