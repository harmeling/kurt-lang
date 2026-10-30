import os
import subprocess
import sys
import tempfile
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# `kurt --profile`: the time and the search steps of each line (plan step 10, dev/todo.md)

TEXT = 'load logic\nprop A, B\nuse A implies B\nuse A\nB\n'


class TestProfile(unittest.TestCase):
    def test_a_check_without_profile_has_none(self):
        self.assertEqual(kurt.Session().check_text(TEXT).profile, [])

    def test_each_line_has_its_time_and_steps(self):
        result = kurt.Session(kurt.RunConfig(profile=True)).check_text(TEXT, 'p.kurt')
        mine = {entry['line']: entry for entry in result.profile if entry['file'] == 'p.kurt'}
        self.assertEqual(sorted(mine), [1, 2, 3, 4, 5])
        self.assertTrue(all(e['seconds'] >= 0 and e['steps'] >= 0 for e in mine.values()))
        self.assertGreater(mine[5]['steps'], 0)        # the line `B` is a search

    def test_the_json_has_the_profile(self):
        result = kurt.Session(kurt.RunConfig(profile=True)).check_text(TEXT, 'p.kurt')
        self.assertIn('"profile"', result.to_json())

    def test_slow_lines(self):
        profile = [{'file': 'p.kurt', 'line': 3, 'seconds': 2.5, 'steps': 900},
                   {'file': 'p.kurt', 'line': 4, 'seconds': 0.1, 'steps': 5},
                   {'file': 'other.kurt', 'line': 3, 'seconds': 9.0, 'steps': 1}]
        self.assertEqual(kurt.slow_lines(profile, 'p.kurt'), {3: (2.5, 900)})
        self.assertEqual(kurt.slow_lines(profile, 'p.kurt', 0.05), {3: (2.5, 900), 4: (0.1, 5)})
        self.assertEqual(kurt.slow_note(2.5, 900), 'slow line: 2.5 s, 900 search steps')

    def test_the_command_line_lists_the_slowest_lines(self):
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, 'p.kurt')
            with open(path, 'w', encoding='utf-8') as f:
                f.write(TEXT)
            env = dict(os.environ, PYTHONPATH=os.path.join(PROJECT_ROOT, 'src'))
            run = subprocess.run([sys.executable, '-m', 'kurt', '--profile', path], capture_output=True, text=True, encoding='utf-8', env=env)
            self.assertIn('the slowest lines of', run.stderr)
            self.assertIn('steps', run.stderr)
            plain = subprocess.run([sys.executable, '-m', 'kurt', path], capture_output=True, text=True, encoding='utf-8', env=env)
            self.assertNotIn('the slowest lines', plain.stderr)
