import builtins
import copy
import io
import os
import contextlib
import tempfile
import unittest

import kurt.kurt as kurt

# `save` writes the input lines that were accepted -- the source itself, which proves its
# results again when checked. In the shell, lines that failed are left out, and so are the ones
# that only show something (`theory`, `cert`, ...). The saved file is always checked by loading it
# into a fresh session.


def load(path: str) -> kurt.KnowledgeBase:
    kb = copy.deepcopy(kurt.initial_kb)
    with contextlib.redirect_stdout(io.StringIO()):
        return kurt.load_file(path, kb, mainstream=False)


def shell(lines: list[str]) -> str:
    # run `lines` as typed into the shell, and return what it printed to stderr (the errors)
    feed = iter(lines)
    def fake_input(prompt=''):
        try:
            return next(feed)
        except StopIteration:
            raise EOFError
    old_input = builtins.input
    builtins.input = fake_input
    stdin = io.StringIO()
    stdin.name = '<stdin>'
    err = io.StringIO()
    try:
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
            kurt.read_eval_loop(stdin, copy.deepcopy(kurt.initial_kb), mainstream=True)
    finally:
        builtins.input = old_input
    return err.getvalue()


class TestSaveCommand(unittest.TestCase):
    def test_save_in_a_file_writes_its_lines(self):
        with tempfile.TemporaryDirectory() as tmp:
            source = os.path.join(tmp, 'source.kurt')
            saved = os.path.join(tmp, 'saved.kurt')
            with open(source, 'w') as fh:
                fh.write(f'load prop\nbool A, B\nuse A implies B "mp"\nuse A\ntheory\n\nshow B\nproof\n    B\nqed\n\nsave "{saved}"\n')
            load(source)
            with open(saved) as fh:
                content = fh.read()
            body = [line for line in content.splitlines() if not line.startswith(';')]
            self.assertEqual(body, ['', 'load prop', 'bool A, B', 'use A implies B "mp"', 'use A', '', 'show B', 'proof', '    B', 'qed', ''])
            labels = {f.label for f in load(saved).theory}
            self.assertIn('mp', labels)

    def test_save_in_the_shell_leaves_out_what_failed(self):
        with tempfile.TemporaryDirectory() as tmp:
            saved = os.path.join(tmp, 'session.kurt')
            errors = shell(['load prop', 'bool A, B', 'use A implies B "mp"', 'B', 'use A', 'theory',
                            'show B', 'proof', '    B', 'qed', f'save "{saved}"'])
            self.assertIn('can not derive', errors)            # `B` before `use A` failed
            with open(saved) as fh:
                body = [line for line in fh.read().splitlines() if line and not line.startswith(';')]
            self.assertEqual(body, ['load prop', 'bool A, B', 'use A implies B "mp"', 'use A', 'show B', 'proof', '    B', 'qed'])
            load(saved)                                         # checks again, without errors

    def test_save_keeps_a_confirmed_expect(self):
        with tempfile.TemporaryDirectory() as tmp:
            saved = os.path.join(tmp, 'session.kurt')
            shell(['load prop', 'bool A', 'expect "ProofError"', '    A', 'use A', f'save "{saved}"'])
            with open(saved) as fh:
                body = [line for line in fh.read().splitlines() if line and not line.startswith(';')]
            self.assertEqual(body, ['load prop', 'bool A', 'expect "ProofError"', '    A', 'use A'])
            load(saved)

    def test_save_needs_closed_blocks(self):
        with tempfile.TemporaryDirectory() as tmp:
            saved = os.path.join(tmp, 'session.kurt')
            errors = shell(['load prop', 'bool A, B', 'show A implies A', f'save "{saved}"',
                            'proof', '    assume A', f'        save "{saved}"'])
            self.assertIn('pending `show`', errors)
            self.assertIn('close the open blocks', errors)
            self.assertFalse(os.path.exists(saved))

    def test_save_writes_only_kurt_files(self):
        # (found in the soundness review of 2026-09-29: `save` could overwrite any file)
        with tempfile.TemporaryDirectory() as tmp:
            victim = os.path.join(tmp, 'victim.txt')
            with open(victim, 'w') as fh:
                fh.write('precious')
            errors = shell(['load prop', f'save "{victim}"', 'save "prop.kurt"'])
            self.assertIn('must end with `.kurt`', errors)
            self.assertIn('is the name of a theory that comes with Kurt', errors)
            with open(victim) as fh:
                self.assertEqual(fh.read(), 'precious')
            self.assertFalse(os.path.exists('prop.kurt'))

    def test_no_save_with_strict_or_in_a_loaded_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            saved = os.path.join(tmp, 'saved.kurt')
            old = kurt.strict_mode
            kurt.strict_mode = True
            try:
                errors = shell(['load prop', f'save "{saved}"'])
            finally:
                kurt.strict_mode = old
            self.assertIn('no `save` with `--strict`', errors)
            helper = os.path.join(tmp, 'helper.kurt')
            with open(helper, 'w') as fh:
                fh.write(f'bool A\nsave "{saved}"\n')
            main = os.path.join(tmp, 'main.kurt')
            with open(main, 'w') as fh:
                fh.write(f'load "{helper}"\n')
            with self.assertRaises(kurt.KurtException) as e:
                load(main)
            self.assertIn('not in a loaded one', e.exception.msg)
            self.assertFalse(os.path.exists(saved))


if __name__ == '__main__':
    unittest.main()
