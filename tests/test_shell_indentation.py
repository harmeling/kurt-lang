import os
import pty
import select
import subprocess
import sys
import time
import unittest

import kurt.kurt as kurt

# at a terminal, the shell fills in the indentation of the current block (one level deeper after
# a line that opens a block), and a backspace dedents -- tested with a pseudo-terminal


def run_shell(keys: list[str], timeout: float = 20.0) -> str:
    main, sub = pty.openpty()
    env = dict(os.environ, PYTHONPATH=os.path.join(os.path.dirname(__file__), '..', 'src'), TERM='dumb', HOME=os.environ.get('TMPDIR', '/tmp'))
    proc = subprocess.Popen([sys.executable, '-m', 'kurt'], stdin=sub, stdout=sub, stderr=sub, env=env, close_fds=True)
    os.close(sub)
    out = b''
    def read_for(seconds: float) -> None:
        nonlocal out
        end = time.time() + seconds
        while time.time() < end:
            r, _, _ = select.select([main], [], [], 0.1)
            if r:
                try:
                    data = os.read(main, 4096)
                except OSError:
                    return
                if not data:
                    return
                out += data
    try:
        read_for(3.0)
        for k in keys:
            os.write(main, k.encode())
            read_for(1.0)
        os.write(main, b'\x04')     # end of input
        read_for(2.0)
    finally:
        proc.kill()
        proc.wait()
        os.close(main)
    return out.decode(errors='replace')


@unittest.skipUnless(sys.platform.startswith('linux') or sys.platform == 'darwin', 'needs a pseudo-terminal')
class TestShellIndentation(unittest.TestCase):
    def test_fill_in_and_dedent(self):
        if kurt.readline_is_libedit():
            # libedit (macOS): no indentation filled in, it is typed (doc/kurt-doc.md, the shell)
            keys = ['load prop\r', 'assume true\r', '    true\r', 'true\r']
        else:
            keys = ['load prop\r',
                    'assume true\r',
                    'true\r',                      # typed without spaces: the shell filled in four
                    '\x7f\x7f\x7f\x7ftrue\r']      # four backspaces: back at the top level
        out = run_shell(keys)
        self.assertIn('open block with assumption', out)
        self.assertIn('true implies true', out.replace('⇒', 'implies'))

class TestLibedit(unittest.TestCase):
    def test_libedit_is_recognized(self):
        # macOS: no indentation filled in, and Tab bound the way of libedit
        import types
        real = kurt.readline
        try:
            for doc, backend, expected in [('Importing this module enables command line editing using libedit readline.', None, True),
                                           ('Importing this module enables command line editing using GNU readline.', None, False),
                                           ('', 'editline', True), ('', 'readline', False)]:
                fake = types.SimpleNamespace(__doc__=doc)
                if backend:
                    fake.backend = backend
                kurt.readline = fake
                self.assertEqual(kurt.readline_is_libedit(), expected)
            kurt.readline = None
            self.assertFalse(kurt.readline_is_libedit())
        finally:
            kurt.readline = real

if __name__ == '__main__':
    unittest.main()
