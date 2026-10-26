import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt

# what a `load` may change in the loading file, and what Kurt makes of a `.kurtc` that is not
# JSON -- the boundary hunt of 2026-10-15


def check(files: dict[str, str], main: str, **config) -> kurt.CheckResult:
    with tempfile.TemporaryDirectory() as tmp:
        for name, text in files.items():
            path = Path(tmp) / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text, encoding='utf-8')
        return kurt.check_file(os.path.join(tmp, main), session=kurt.Session(kurt.RunConfig(**config)))


class TestWithdrawnClaims(unittest.TestCase):
    def test_a_withdrawn_claim_is_a_todo(self):
        # `show B`, `break` left nothing open and nothing to do: a file of withdrawn claims was
        # "complete", and the grader gave it full marks
        result = kurt.check_text('load propositional\nprop A, B\nuse A\nshow B\nbreak\nshow A and A\nproof\n    break\nbreak\n')
        self.assertTrue(result.ok, result.error)
        self.assertFalse(result.complete)
        self.assertEqual(len(result.todos), 2)
        self.assertIn('withdrew the claim `B`', result.todos[0])
        self.assertIn('Proof almost checked: 2 todos.', result.output)

    def test_a_proof_given_up_and_done_again_is_not_a_todo(self):
        result = kurt.check_text('load propositional\nprop A\nuse A\nshow A and A\nproof\n    break\nproof\n    A and A\nqed\n')
        self.assertTrue(result.complete, result.error)


class TestAliasAcrossLoad(unittest.TestCase):
    def test_a_loaded_file_can_not_alias_the_loaders_symbol(self):
        # `const foo` and a fact about it here, `alias foo bar` in the loaded file: `foo = d` was
        # then proved "by bd", a fact about `bar` (the mirror image of doc/kurt-soundness.md §8.36)
        result = check({'lib.kurt': 'load equality\nconst bar, d\nalias foo bar\nuse bar = d "bd"\n',
                        'main.kurt': 'load equality\nconst foo, d\nuse foo ≠ d "fd"\nload lib\nfoo = d\n'}, 'main.kurt')
        self.assertFalse(result.ok)
        self.assertIn('`foo` is a symbol of its own here, but an alias of `bar` in `lib.kurt`', result.error or '')

    def test_the_same_alias_on_both_sides_is_fine(self):
        # (a theory loaded twice brings its aliases twice)
        result = check({'lib.kurt': 'load numbers\nconst c\nuse c >= 1 "c1"\n',
                        'main.kurt': 'load numbers\nconst d\nuse d >= 2\nload lib\nc >= 1\n'}, 'main.kurt')
        self.assertTrue(result.ok, result.error)


class TestLocalDeclarations(unittest.TestCase):
    def test_a_local_constant_in_an_exported_fact_is_refused(self):
        # `const q local`, `use q "pq"`: the fact took `q` along, and the `local` meant nothing
        result = check({'lib.kurt': 'load propositional\nconst q local\nprop q\nuse q "pq"\n', 'main.kurt': 'load lib\nq\n'}, 'main.kurt')
        self.assertFalse(result.ok)
        self.assertIn("symbol(s) ['q'] are declared `local` but required by an exported fact", result.error or '')

    def test_a_local_constant_in_a_local_fact_stays_in_the_file(self):
        result = check({'lib.kurt': 'load propositional\nconst q local\nprop q\nuse q local "pq"\nprop P\nuse P "p"\n',
                        'main.kurt': 'load lib\nP\nexpect "ProofError"\n    q\n'}, 'main.kurt')
        self.assertTrue(result.ok, result.error)


class TestTermsAndStatementsAcrossLoad(unittest.TestCase):
    def test_a_statement_here_and_a_term_there_is_refused(self):
        # `prop Nat`, then `load natural` was accepted (the other declarations before a `load` are refused)
        result = kurt.check_text('load set\nprop Nat\nload natural\n')
        self.assertFalse(result.ok)
        self.assertIn('`Nat` is a statement here (`prop Nat`), but a term in `natural.kurt`', result.error or '')
        result = check({'lib.kurt': 'load propositional\nprop P\nuse P "p"\n', 'main.kurt': 'load equality\nconst P\nuse P = P\nload lib\n'}, 'main.kurt')
        self.assertFalse(result.ok)
        self.assertIn('`P` is a term here, but a statement (`prop P`) in `lib.kurt`', result.error or '')


class TestOneFileOneName(unittest.TestCase):
    def test_a_file_loaded_under_two_spellings_is_one_file(self):
        # `lib/op.kurt` and `lib/../lib/op.kurt`: "`opl` is declared in `op.kurt` and in `op.kurt`"
        result = check({'lib/op.kurt': 'infix opl 50 50\nconst a\nuse a opl a "aa"\n',
                        'main.kurt': 'load lib/op\nload lib/../lib/op\nload ./lib/op\na opl a\n'}, 'main.kurt')
        self.assertTrue(result.ok, result.error)
        self.assertEqual(result.output.count('already loaded'), 2, result.output)


class TestSymlinks(unittest.TestCase):
    def test_a_file_through_a_symlink_is_the_same_file(self):
        # `lib2 -> lib`: `load lib/op` and `load lib2/op` counted as two files ("declared in `op.kurt` and in `op.kurt`")
        with tempfile.TemporaryDirectory() as tmp:
            os.mkdir(os.path.join(tmp, 'lib'))
            Path(tmp, 'lib', 'op.kurt').write_text('infix opl 50 50\nconst a\nuse a opl a "aa"\n', encoding='utf-8')
            os.symlink(os.path.join(tmp, 'lib'), os.path.join(tmp, 'lib2'))
            Path(tmp, 'main.kurt').write_text('load lib/op\nload lib2/op\na opl a\n', encoding='utf-8')
            result = kurt.check_file(os.path.join(tmp, 'main.kurt'))
            self.assertTrue(result.ok, result.error)
            self.assertIn('already loaded', result.output)


    def test_a_file_in_a_symlinked_directory_keeps_its_name(self):
        # macOS: the temporary directory `/var/...` is a symlink to `/private/var/...`; resolving
        # symlinks in the names of loaded files renamed them, so the main file's steps were taken for
        # another file's -- `kurt --lean` wrote no theorem, the hover linked the wrong path (CI, macOS,
        # 2026-10-15 to -17). The same layout here: `link -> real`
        with tempfile.TemporaryDirectory() as tmp:
            os.mkdir(os.path.join(tmp, 'real'))
            link = os.path.join(tmp, 'link')
            os.symlink(os.path.join(tmp, 'real'), link)
            Path(link, 'lib.kurt').write_text('load propositional\nprop P\nuse P "p"\n', encoding='utf-8')
            main = os.path.join(link, 'main.kurt')
            Path(main).write_text('load propositional\nload lib\nprop A\nuse A implies P\nshow A implies P "ap"\nproof\n    assume A\n        P\nqed\n', encoding='utf-8')
            result = kurt.check_file(main)
            self.assertTrue(result.ok, result.error)
            self.assertIn(os.path.join(link, 'lib.kurt'), result.loaded)
            done = subprocess.run([sys.executable, '-m', 'kurt.kurt', '--no-kurtc', '--lean', main, '-o', '-'],
                                  capture_output=True, text=True, env={**os.environ, 'PYTHONPATH': str(Path(kurt.__file__).parents[1])})
            self.assertEqual(done.returncode, 0, done.stderr)
            self.assertIn('theorem ', done.stdout)


class TestDamagedCertificates(unittest.TestCase):
    def test_a_kurtc_nested_too_deep_is_damaged_not_a_crash(self):
        # json's RecursionError was not caught: a traceback, also for `kurt FILE.kurtc` and `--deps`
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'mp.kurt'
            path.write_text('prop A, B\nuse A implies B "ab"\nuse A "a"\nB\n', encoding='utf-8')
            Path(str(path) + 'c').write_text('[' * 200000 + ']' * 200000, encoding='utf-8')
            self.assertEqual(kurt.kurtc_status(str(path)), 'not certified (the `.kurtc` is damaged)')
            result = kurt.check_file(str(path), session=kurt.Session(kurt.RunConfig(kurtc=True)))
            self.assertTrue(result.ok, result.error)
            content = json.loads(Path(str(path) + 'c').read_text(encoding='utf-8'))   # written again, good now
            self.assertEqual(content['kurtc'], kurt.KURTC_VERSION)


if __name__ == '__main__':
    unittest.main()
