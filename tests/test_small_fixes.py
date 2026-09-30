import contextlib
import copy
import io
import os
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# three small bugs found in dev/codex-suggestions.md (2026-09-29)


def check(text: str) -> tuple[str, str]:
    # check `text` as a file, and return what it printed to stdout and stderr
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'f.kurt')
        with open(path, 'w') as fh:
            fh.write(text)
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            kurt.load_file(path, copy.deepcopy(kurt.initial_kb), mainstream=True)
        return out.getvalue(), err.getvalue()


class TestSmallFixes(unittest.TestCase):
    def test_parse_reports_a_type_error_and_goes_on(self):
        # `keyword_token in ['parse']` compared a `Token` with a string: never true
        out, err = check('bool P\narity P 1\nparse P (1 implies 2)\ntrue\n')
        self.assertIn('type check failed', err)
        self.assertIn('(P (implies 1 2))', out)

    def test_each_definition_of_a_line_is_logged(self):
        # all of them were logged as the last one
        out, _ = check('load equality\ndef a = 1, b = 2\n')
        self.assertIn('def a = 1', out)
        self.assertIn('def b = 2', out)

    def test_history_file_is_read_and_problems_are_ignored(self):
        # reading the history was switched off (`and False`); an unreadable file is no error
        env = dict(os.environ)
        env['PYTHONPATH'] = str(PROJECT_ROOT / 'src') + os.pathsep + env.get('PYTHONPATH', '')
        with tempfile.TemporaryDirectory() as home:
            env['HOME'] = home
            history = os.path.join(home, '.kurt_history')
            for mode in (0o644, 0o000):
                with open(history, 'w') as fh:
                    fh.write('bool A\n')
                os.chmod(history, mode)
                result = subprocess.run([sys.executable, '-m', 'kurt.kurt'], input='bool B\n', env=env,
                                        capture_output=True, text=True, timeout=30)
                os.chmod(history, 0o644)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertNotIn('Traceback', result.stderr)


if __name__ == '__main__':
    unittest.main()
