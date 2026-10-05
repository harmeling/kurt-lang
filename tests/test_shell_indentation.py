import os
import pty
import select
import subprocess
import sys
import time
import unittest

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
        out = run_shell([
            'load prop\r',
            'assume true\r',
            'true\r',                      # typed without spaces: the shell filled in four
            '\x7f\x7f\x7f\x7ftrue\r',      # four backspaces: back at the top level
        ])
        self.assertIn('open block with assumption', out)
        self.assertIn('true implies true', out.replace('⇒', 'implies'))

if __name__ == '__main__':
    unittest.main()
