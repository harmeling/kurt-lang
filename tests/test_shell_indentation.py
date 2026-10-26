import os
import pty
import select
import subprocess
import sys
import tempfile
import time
import unittest


# at a terminal, the shell fills in the indentation of the current block (one level deeper after
# a line that opens a block), and a backspace dedents -- tested with a pseudo-terminal


def run_shell(keys: list[str], timeout: float = 20.0, home: 'str | None' = None) -> str:
    # each key is typed once the shell waits for it (its prompt `;[N] ` is shown): the shell
    # reads keys raw only while it waits for a line -- a key typed while a line is still checked
    # (a cold `load propositional` on a busy node takes seconds) would go through the terminal's line
    # editing (a backspace lost, Ctrl-C a signal). HOME is a fresh directory: `~/.kurt_history`
    # is written at the exit (it was /tmp/.kurt_history, shared by everyone on the machine) --
    # pass `home` to inspect it afterwards (e.g. whether it was written at all, todo 33(a))
    main, sub = pty.openpty()
    own_home = None
    if home is None:
        own_home = tempfile.TemporaryDirectory()
        home = own_home.name
    env = dict(os.environ, PYTHONPATH=os.path.join(os.path.dirname(__file__), '..', 'src'), TERM='dumb',
               HOME=home)
    proc = subprocess.Popen([sys.executable, '-m', 'kurt'], stdin=sub, stdout=sub, stderr=sub, env=env, close_fds=True)
    os.close(sub)
    out = b''
    def read_until(seconds: float, until: bytes | None = None) -> None:
        # until `until` was printed, or the end of the output
        nonlocal out
        end = time.time() + seconds
        while time.time() < end and (until is None or until not in out):
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
        line = 1
        read_until(timeout, b';[1] ')
        for k in keys:
            os.write(main, k.encode())
            line += k.count('\r')
            read_until(timeout, f';[{line}] '.encode())
        os.write(main, b'\x04')     # end of input
        read_until(timeout)          # (until the shell has ended)
    finally:
        proc.kill()
        proc.wait()
        os.close(main)
        if own_home is not None:
            own_home.cleanup()
    return out.decode(errors='replace')


@unittest.skipUnless(sys.platform.startswith('linux') or sys.platform == 'darwin', 'needs a pseudo-terminal')
class TestShellIndentation(unittest.TestCase):
    def test_fill_in_and_dedent(self):
        # the same on macOS now (todo 27: the shell's own line editor, no libedit)
        keys = ['load propositional\r',
                'assume true\r',
                'true\r',                      # typed without spaces: the shell filled in four
                '\x7ftrue\r']                  # one backspace: back at the top level
        out = run_shell(keys)
        self.assertIn('open block with assumption', out)
        self.assertIn('true implies true', out.replace('⇒', 'implies'))

    def test_history_tab_and_ctrl_c(self):
        out = run_shell(['load propositional\r',
                         'prop A\r',
                         'use A\r',
                         '\x1b[A\r',                   # ↑: `use A` again -- one more axiom
                         'garbage\x03',                # Ctrl-C: the line is dropped
                         '\\top\t\r'])                 # Tab: `⊤`
        self.assertEqual(out.count('without proof'), 2, out)
        self.assertIn('^C', out)
        self.assertNotIn('garbage', out.split('^C')[-1])
        self.assertIn('by top-intro', out)


@unittest.skipUnless(sys.platform.startswith('linux') or sys.platform == 'darwin', 'needs a pseudo-terminal')
class TestHistoryWrittenOnlyWhenChanged(unittest.TestCase):
    # `~/.kurt_history` used to be rewritten at the exit of every run, even a non-interactive one
    # (`kurt FILE`, piped input) that never touches `shell_history` at all (dev/todo.md #33(a)):
    # write it back only if the shell actually changed it during the run

    def test_interactive_session_still_writes_new_lines(self):
        with tempfile.TemporaryDirectory() as home:
            run_shell(['load propositional\r', 'prop A\r'], home=home)
            history = os.path.join(home, '.kurt_history')
            self.assertTrue(os.path.exists(history))
            with open(history) as fh:
                content = fh.read()
            self.assertIn('load propositional', content)
            self.assertIn('prop A', content)

    def test_a_session_that_adds_nothing_does_not_rewrite_the_file(self):
        # an interactive session that is started and immediately ended (Ctrl-D at the first
        # prompt, before a line is typed) reads the history but never appends to it -- the file
        # must come out exactly as it went in, not merely with the same content rewritten
        with tempfile.TemporaryDirectory() as home:
            history = os.path.join(home, '.kurt_history')
            with open(history, 'w') as fh:
                fh.write('load propositional\nprop A\n')
            before_mtime = os.stat(history).st_mtime_ns
            with open(history) as fh:
                before_content = fh.read()
            run_shell([], home=home)
            self.assertEqual(os.stat(history).st_mtime_ns, before_mtime)
            with open(history) as fh:
                self.assertEqual(fh.read(), before_content)


if __name__ == '__main__':
    unittest.main()
