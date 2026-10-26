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

# three small bugs found in dev/codex-suggestions.md, in git history (2026-09-29)


def check(text: str) -> tuple[str, str]:
    # check `text` as a file, and return what it printed to stdout and stderr
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'f.kurt')
        with open(path, 'w') as fh:
            fh.write(text)
        out, err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
            kurt.load_file(path, copy.deepcopy(kurt.initial_kb), main=True)
        return out.getvalue(), err.getvalue()


class TestSmallFixes(unittest.TestCase):
    def test_parse_reports_a_type_error_and_goes_on(self):
        # `keyword_token in ['parse']` compared a `Token` with a string: never true
        out, err = check('prop P\narity P 1\nparse P (1 implies 2)\ntrue\n')
        self.assertIn('type check failed', err)
        self.assertIn('(P (implies 1 2))', out)

    def test_type_error_parsed_as_is_captured_not_leaked_to_stderr(self):
        # "(the line was read as ...)" after a `TypeError` used to go straight to the real
        # `sys.stderr` with a raw `print`, bypassing `check_text`'s output capture entirely --
        # invisible to a library caller (the LSP, the playground, a grader) and polluting the
        # host process's own stderr (dev/todo.md #33(c))
        out = io.StringIO()
        with contextlib.redirect_stderr(out):
            result = kurt.check_text('prop P\narity P 1\nP (1 implies 2)\n')
        self.assertFalse(result.ok)
        self.assertIn('(the line was read as `P (1 implies 2)`)', result.error or '')
        self.assertEqual(out.getvalue(), '')     # nothing leaked to the real stderr

    def test_each_definition_of_a_line_is_logged(self):
        # all of them were logged as the last one
        out, _ = check('load equality\ndef a = 1, b = 2\n')
        self.assertIn('def a = 1', out)
        self.assertIn('def b = 2', out)

    def test_history_file_is_read_and_problems_are_ignored(self):
        # reading the history was switched off once (`and False`); an unreadable file is no error;
        # a file of readline or libedit (`_HiStOrY_V2_`, `\\040` for a space) is read too
        with tempfile.TemporaryDirectory() as home:
            history = os.path.join(home, '.kurt_history')
            with open(history, 'w') as fh:
                fh.write('_HiStOrY_V2_\nprop\\040A\n\nuse\\040A\n')
            self.assertEqual(kurt.read_history(history), ['prop A', 'use A'])
            os.chmod(history, 0o000)
            try:
                if os.geteuid() != 0:                       # (root reads it anyway)
                    self.assertEqual(kurt.read_history(history), [])
            finally:
                os.chmod(history, 0o644)
            self.assertEqual(kurt.read_history(os.path.join(home, 'none')), [])

    def test_a_run_without_the_shell_leaves_the_history_as_it_is(self):
        # `kurt FILE`, piped input, `--json` rewrote ~/.kurt_history at every exit -- truncated,
        # converted from libedit's format -- also from the tests (todo 33); now only the shell's lines change it
        env = dict(os.environ)
        env['PYTHONPATH'] = str(PROJECT_ROOT / 'src') + os.pathsep + env.get('PYTHONPATH', '')
        with tempfile.TemporaryDirectory() as home:
            env['HOME'] = home
            history = os.path.join(home, '.kurt_history')
            content = '_HiStOrY_V2_\nprop\\040A\n'
            for mode in (0o644, 0o000):
                with open(history, 'w') as fh:
                    fh.write(content)
                os.chmod(history, mode)
                proof = os.path.join(home, 'p.kurt')
                with open(proof, 'w') as fh:
                    fh.write('prop C\nuse C\nC\n')
                for args, text in ((['-m', 'kurt.kurt'], 'prop B\n'), (['-m', 'kurt.kurt', '--no-kurtc', proof], ''),
                                   (['-m', 'kurt.kurt', '--no-kurtc', '--json', proof], '')):
                    result = subprocess.run([sys.executable, *args], input=text, env=env, capture_output=True, text=True, timeout=30)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertNotIn('Traceback', result.stderr)
                os.chmod(history, 0o644)
                with open(history) as fh:
                    self.assertEqual(fh.read(), content)
            # a history the shell added to is written, one it didn't isn't
            kurt.write_history_if_changed(['prop A'], ['prop A'], history)
            with open(history) as fh:
                self.assertEqual(fh.read(), content)
            kurt.write_history_if_changed(['prop A', 'prop D'], ['prop A'], history)
            with open(history) as fh:
                self.assertEqual(fh.read(), 'prop A\nprop D\n')

    def test_history_untouched_by_a_non_interactive_run(self):
        # `kurt FILE` and piped input never open an interactive terminal, so `shell_history` never
        # changes -- the file must come back byte-for-byte identical, not merely "still has the
        # line" (it used to be truncated to 1000 lines and reformatted on every run, dev/todo.md
        # #33(a))
        env = dict(os.environ)
        env['PYTHONPATH'] = str(PROJECT_ROOT / 'src') + os.pathsep + env.get('PYTHONPATH', '')
        with tempfile.TemporaryDirectory() as home, tempfile.TemporaryDirectory() as proj:
            env['HOME'] = home
            history = os.path.join(home, '.kurt_history')
            with open(history, 'w') as fh:
                fh.write('load propositional\nuse A\n')
            before_mtime = os.stat(history).st_mtime_ns
            with open(history) as fh:
                before_content = fh.read()
            path = os.path.join(proj, 'f.kurt')
            with open(path, 'w') as fh:
                fh.write('load propositional\nprop B\nuse B\n')
            result = subprocess.run([sys.executable, '-m', 'kurt.kurt', path], env=env,
                                    capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(os.stat(history).st_mtime_ns, before_mtime)
            with open(history) as fh:
                self.assertEqual(fh.read(), before_content)

    def test_the_reading_of_a_line_with_a_type_error_is_part_of_the_error(self):
        # "parsed as: ..." went straight to stderr, outside what `check_text` reports (todo 33)
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            result = kurt.check_text('load propositional\nprop P\narity P 2\nuse not P\n')
        self.assertEqual(err.getvalue(), '')
        self.assertIn('TypeError', result.error or '')
        self.assertIn('(the line was read as `not P`)', result.error or '')

if __name__ == '__main__':
    unittest.main()
