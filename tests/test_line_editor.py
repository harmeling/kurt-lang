import os
import tempfile
import unittest

import kurt.kurt as kurt

# the shell's own line editor (todo 27, 2026-10-14; before: `readline`, which macOS's libedit and
# Windows didn't have as GNU readline): `LineEditor` takes keys and says what to draw, so it is
# tested here without a terminal; tests/test_shell_indentation.py drives the shell in a pty


def typed(editor: kurt.LineEditor, text: str) -> None:
    for c in text:
        editor.key(c)


class TestLineEditor(unittest.TestCase):
    def test_the_indentation_is_filled_in_and_a_backspace_dedents(self):
        e = kurt.LineEditor()
        e.start(';[1] ', '        ')
        typed(e, 'true')
        self.assertEqual(e.text, '        true')
        e.start(';[1] ', '        ')
        e.key('backspace')                                 # over the indentation: one level
        self.assertEqual(e.text, '    ')
        e.key('backspace')
        e.key('backspace')                                 # (at the start: nothing more)
        self.assertEqual(e.text, '')
        e.start(';[1] ', '  ')                             # (not a full level: to the level before)
        e.key('backspace')
        self.assertEqual(e.text, '')

    def test_editing(self):
        e = kurt.LineEditor()
        e.start('> ')
        typed(e, 'show A')
        e.key('home')
        e.key('delete')
        self.assertEqual(e.text, 'how A')
        e.key('ctrl-e')
        e.key('left')
        typed(e, '∀')                                      # one character, also in UTF-8
        self.assertEqual((e.text, e.cursor), ('how ∀A', 5))
        e.key('ctrl-k')
        self.assertEqual(e.text, 'how ∀')
        e.key('ctrl-w')
        self.assertEqual(e.text, 'how ')
        e.key('ctrl-a')
        e.key('right')
        e.key('ctrl-u')
        self.assertEqual((e.text, e.cursor), ('ow ', 0))

    def test_the_history(self):
        e = kurt.LineEditor(['load prop', 'show A implies A', 'assume A'])
        e.start('> ')
        typed(e, 'dra')
        e.key('up')
        self.assertEqual(e.text, 'assume A')
        e.key('up')
        e.key('up')
        e.key('up')                                        # (the oldest: stays)
        self.assertEqual(e.text, 'load prop')
        for _ in range(3):
            e.key('down')
        self.assertEqual(e.text, 'dra')                    # back to the line being written
        e.key('ctrl-r')                                    # search
        typed(e, 'A')
        self.assertEqual(e.text, 'assume A')
        e.key('ctrl-r')                                    # the one before
        self.assertEqual(e.text, 'show A implies A')
        e.key('end')                                       # leave the search with it
        typed(e, '!')
        self.assertEqual(e.text, 'show A implies A!')

    def test_tab_completes(self):
        e = kurt.LineEditor(completer=lambda line, word: [c for c in ('\\forall', '\\for') if c.startswith(word)])
        e.start('> ')
        typed(e, 'show \\fo')
        e.key('tab')                                       # what they have in common
        self.assertEqual((e.text, e.listing), ('show \\for', []))
        e.key('tab')                                       # again: the list, below the line
        self.assertEqual(e.listing, ['\\forall', '\\for'])
        self.assertIn('\\forall  \\for\r\n', e.render(80))
        e.completer = lambda line, word: ['∀'] if word == '\\forall' else []
        e.start('> ')
        typed(e, '\\forall')
        e.key('tab')
        self.assertEqual(e.text, '∀ ')

    def test_enter_ctrl_c_ctrl_d(self):
        e = kurt.LineEditor()
        e.start('> ', '    ')
        self.assertEqual(e.key('ctrl-d'), 'eof')           # an empty line (only the indentation): the end
        typed(e, 'xy')
        e.key('left')
        self.assertIsNone(e.key('ctrl-d'))                 # else: delete
        self.assertEqual(e.text, '    x')
        self.assertEqual(e.key('ctrl-c'), 'interrupt')
        self.assertEqual(e.key('enter'), 'accept')

    def test_drawing_a_long_line(self):
        # back to the start of the line as it was drawn, clear to the end of the screen, the
        # prompt and the text, the cursor to its place: two rows up, column 4
        e = kurt.LineEditor()
        e.start(';[1] ')
        typed(e, 'x' * 20)
        e.key('left')
        self.assertEqual(e.render(10), '\r\x1b[J;[1] ' + 'x' * 20 + '\r\x1b[4C')
        e.key('home')
        self.assertEqual(e.render(10), '\x1b[2A\r\x1b[J;[1] ' + 'x' * 20 + '\x1b[2A\r\x1b[5C')

    def test_the_keys_of_a_terminal(self):
        keys, rest = kurt.terminal_keys('ab\x1b[A\x1b[3~\r\nc∀\x1b[1;5C\x7f\x1b')
        self.assertEqual(keys, ['a', 'b', 'up', 'delete', 'enter', 'c', '∀', 'backspace'])
        self.assertEqual(rest, '\x1b')                     # (the rest of a sequence may follow)
        keys, _ = kurt.terminal_keys('\x1b[200~line 1\nline 2\x1b[201~')   # pasted: line by line
        self.assertEqual(keys.count('enter'), 1)

    def test_the_history_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'history')
            kurt.write_history(['load prop', 'show A'], path)
            self.assertEqual(kurt.read_history(path), ['load prop', 'show A'])
            with open(path, 'w', encoding='utf-8') as f:     # as libedit wrote it (macOS)
                f.write('_HiStOrY_V2_\nload\\040prop\nshow\\040A\n')
            self.assertEqual(kurt.read_history(path), ['load prop', 'show A'])
            self.assertEqual(kurt.read_history(os.path.join(tmp, 'none')), [])


if __name__ == '__main__':
    unittest.main()
