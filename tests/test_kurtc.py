import copy
import io
import json
import contextlib
import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt


class KurtcTestCase(unittest.TestCase):
    # runs files in a temporary directory, with `.kurtc` files on (as `kurt` on the command line)
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.old = kurt.kurtc_enabled
        kurt.kurtc_enabled = True

    def tearDown(self):
        kurt.kurtc_enabled = self.old
        kurt.replay_hints.clear()
        self.dir.cleanup()

    def write(self, name: str, text: str) -> Path:
        path = Path(self.dir.name) / name
        path.write_text(text)
        return path

    def run_file(self, path: Path) -> str:
        kb = copy.deepcopy(kurt.initial_kb)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            kurt.load_file(str(path), kb, mainstream=True)
        return out.getvalue()


class TestWriting(KurtcTestCase):
    def test_a_checked_file_gets_a_kurtc(self):
        path = self.write('mp.kurt', 'bool A, B\nuse A implies B\nuse A\nB\n')
        self.run_file(path)
        content = json.loads(Path(str(path) + 'c').read_text())
        self.assertEqual(content['kurtc'], kurt.KURTC_VERSION)
        self.assertEqual(content['sha256'], kurt.source_hash(str(path)))
        self.assertEqual(list(content['steps']), ['4'])
        step = content['steps']['4'][0]
        self.assertEqual(step['rule']['line'], '2')
        self.assertEqual([f['line'] for f in step['facts']], ['3'])

    def test_no_kurtc_with_a_todo(self):
        path = self.write('todo.kurt', 'bool A\ntodo\nA\n')
        self.run_file(path)
        self.assertFalse(Path(str(path) + 'c').exists())

    def test_dependencies_are_listed(self):
        self.write('lemma.kurt', 'bool A\nuse A "a"\n')
        path = self.write('main.kurt', 'load lemma\nA\n')
        self.run_file(path)
        content = json.loads(Path(str(path) + 'c').read_text())
        self.assertEqual([Path(d['file']).name for d in content['depends']], ['lemma.kurt'])


if __name__ == '__main__':
    unittest.main()
