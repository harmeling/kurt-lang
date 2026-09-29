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


class TestReplay(KurtcTestCase):
    def count_searches(self, path: Path) -> tuple[str, int]:
        # the output, and how often the search (`impl_elim`) runs
        calls = [0]
        impl_elim = kurt.impl_elim
        def counting(*args):
            calls[0] += 1
            return impl_elim(*args)
        kurt.impl_elim = counting
        try:
            return self.run_file(path), calls[0]
        finally:
            kurt.impl_elim = impl_elim

    def test_second_run_needs_no_search(self):
        path = self.write('eq.kurt', 'load equality\nconst a, b, f\narity f 1\nuse a = b\nuse f a = a\nf b = a\nb = a\n')
        out1, searches1 = self.count_searches(path)
        out2, searches2 = self.count_searches(path)
        self.assertEqual(out1, out2)
        self.assertGreater(searches1, 0)
        self.assertEqual(searches2, 0)

    def test_changed_source_ignores_the_kurtc(self):
        path = self.write('mp.kurt', 'bool A, B\nuse A implies B\nuse A\nB\n')
        self.run_file(path)
        path.write_text('bool A, B\nuse A implies B\nuse A\nB\nB\n')
        _, searches = self.count_searches(path)
        self.assertGreater(searches, 0)

    def test_forged_kurtc_proves_nothing(self):
        # a `.kurtc` with the right hash, but a certificate for a false claim: `B` from `A`
        good = self.write('good.kurt', 'bool A, B\nuse A implies B\nuse A\nB\n')
        self.run_file(good)
        forged = json.loads(Path(str(good) + 'c').read_text())
        bad = self.write('bad.kurt', 'bool A, B\nuse B implies A\nuse A\nB\n')     # `B` doesn't follow
        forged['sha256'] = kurt.source_hash(str(bad))
        forged['steps']['4'][0]['rule']['file'] = str(bad)
        forged['steps']['4'][0]['facts'][0]['file'] = str(bad)
        # the stored rule is exactly line 2 of `bad.kurt`, so it is found -- only the kernel can object
        forged['steps']['4'][0]['rule']['expr'] = {'e': [['SYMBOL', 'implies'], ['SYMBOL', 'B'], ['SYMBOL', 'A']]}
        Path(str(bad) + 'c').write_text(json.dumps(forged))
        verdicts = []
        verify = kurt.kernel_verify
        def recording(cert, kb):
            verdicts.append(verify(cert, kb))
            return verdicts[-1]
        kurt.kernel_verify = recording
        try:
            with self.assertRaises(kurt.KurtException) as e:
                self.run_file(bad)
        finally:
            kurt.kernel_verify = verify
        self.assertIn('can not derive', e.exception.msg)
        self.assertTrue(any(v is not None and 'not the goal' in v for v in verdicts), verdicts)   # the kernel said no

    def test_damaged_kurtc_is_ignored(self):
        path = self.write('mp.kurt', 'bool A, B\nuse A implies B\nuse A\nB\n')
        self.run_file(path)
        content = json.loads(Path(str(path) + 'c').read_text())
        content['steps']['4'][0]['values'] = 'nonsense'
        Path(str(path) + 'c').write_text(json.dumps(content))
        self.assertIn('B                                         ; 4 by 3, 2', self.run_file(path))


class TestDependencies(KurtcTestCase):
    def test_tree_with_status(self):
        self.write('a.kurt', 'bool A\nuse A "a"\n')
        self.write('b.kurt', 'load a\nbool B\nuse A implies B "b"\n')
        main = self.write('main.kurt', 'load a, b\nB\n')
        self.assertIn('main.kurt  -- not certified', kurt.dependencies_str(str(main)))
        self.run_file(main)
        tree = kurt.dependencies_str(str(main)).splitlines()
        self.assertTrue(tree[0].startswith('main.kurt  -- certified'), tree)
        self.assertTrue(tree[1].startswith('├─ a.kurt  -- certified'), tree)
        self.assertTrue(tree[2].startswith('└─ b.kurt  -- certified'), tree)
        self.assertEqual(tree[3], '   └─ a.kurt  (see above)')
        (Path(self.dir.name) / 'a.kurt').write_text('bool A\nuse A "a"\n; changed\n')
        tree = kurt.dependencies_str(str(main)).splitlines()
        self.assertIn('certified, but a.kurt changed since', tree[0])
        self.assertIn('out of date: the file changed since', tree[1])


if __name__ == '__main__':
    unittest.main()
