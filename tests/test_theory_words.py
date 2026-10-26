import copy
import glob
import os
import unittest

import kurt.kurt as kurt

# todo 61: in Kurt's own theories the standard name of a symbol is ASCII, a word (`union`), and the
# Unicode symbol is its alias (`∪`); a line is printed as written, with the one or the other

THEORIES = os.path.join(os.path.dirname(kurt.__file__), 'theories')

# the words of the theories, with their symbols (doc/kurt-ref.md, the table of the words)
WORDS = {
    'set.kurt': {'∪': 'union', '∩': 'intersect', '∅': 'emptyset', '⊂': 'subset', '⊃': 'superset', '∉': 'notin',
                 '×': 'cross', '→': 'to', '∈': 'in'},
    'equality.kurt': {'≠': 'neq'},
    'natural.kurt': {'∣': 'divides'},
    'field.kurt': {'·': 'times'},
    'matrix.kurt': {'·': 'times'},
    'group.kurt': {'∘': 'compose'},
    'finite.kurt': {'∖': 'setminus'},
    'lambda.kurt': {'λ': 'lambda', '↦': 'reduces', '⇝': 'steps', '⊢': 'proves'},
    'modal.kurt': {'→': 'imp', '⇔': 'equiv', '∧': 'wedge', '∨': 'vee', '¬': 'neg', '⊥': 'bot', '□': 'box',
                   '◇': 'diamond', '⊢': 'proves'},
}

GREEK = set('αβγδεζηθικλμνξοπρστυφχψωΓΔΘΛΞΠΣΦΨΩ')


def loaded(name: str) -> kurt.KnowledgeBase:
    return kurt.load_file(name, copy.deepcopy(kurt.initial_kb), main=False)


class TestTheoryWords(unittest.TestCase):
    def test_every_symbol_of_the_theories_is_ascii(self):
        # a symbol of a theory that isn't an alias has an ASCII name -- but a Greek letter that is
        # a variable (group.kurt's `ι`): a name, not an operator
        for path in sorted(glob.glob(os.path.join(THEORIES, '*.kurt'))):
            name = os.path.basename(path)
            kb = copy.deepcopy(kurt.initial_kb) if name == 'minimal.kurt' else loaded(name)
            declared: set[str] = set()
            aliases: set[str] = set()
            for node in kb.levels():
                declared |= node.declared_symbols()
                aliases |= set(node.alias)
            unicode = sorted(s for s in declared - aliases if not s.isascii() and not set(s) <= GREEK)
            self.assertEqual(unicode, [], f'{name}: symbols without an ASCII name')

    def test_the_words_and_their_aliases(self):
        for name, words in WORDS.items():
            kb = loaded(name)
            for symbol, word in words.items():
                self.assertEqual(kb.get_alias(symbol), word, f'{name}: {symbol}')
                self.assertTrue(kb.is_known(word), f'{name}: {word}')

    def test_both_names_mean_the_same_and_print_as_written(self):
        result = kurt.check_text(
            'load set\n'
            'const A, B, x\n'
            'use x ∈ A ∪ B "u"\n'
            'x in A union B\n'
            'use A ∩ B ⊂ A "s"\n'
            'A intersect B subset A\n')
        self.assertTrue(result.ok, result.error)
        out = result.output
        self.assertIn('x ∈ (A ∪ B) ', out)              # as written, with the symbols ...
        self.assertIn('x in (A union B) ', out)         # ... and with the words
        self.assertIn('(A intersect B) subset A ', out)
        self.assertNotIn('x in (A ∪ B)', out)

    def test_a_loading_file_means_the_theorys_symbol(self):
        # across `load`: `∪` of a loading file is set.kurt's `union`; a symbol `union` of its own clashes
        kb = loaded('set.kurt')
        tokens = list(kurt.scan_string('A ∪ ∅', kb))
        self.assertEqual([(t.value, t.origin) for t in tokens][:3], [('A', None), ('union', '∪'), ('emptyset', '∅')])
        result = kurt.check_text('load set\nconst union\n')
        self.assertFalse(result.ok)

    def test_latex_of_the_word_and_the_symbol(self):
        kb = loaded('set.kurt')
        self.assertEqual(kurt.tex_line('A ∪ B', kb), kurt.tex_line('A union B', kb))
        self.assertIn(r'\cup', kurt.tex_line('A union B', kb) or '')
        self.assertIn(r'\neq', kurt.tex_line('A ≠ ∅', kb) or '')
        self.assertIn(r'\emptyset', kurt.tex_line('A neq emptyset', kb) or '')

    def test_a_declaration_with_the_alias_is_about_the_word(self):
        # `tex ∪ ...` (a file's own LaTeX for the theory's symbol) is about `union`, and shown as written
        result = kurt.check_text('load set\ntex ∪ \\sqcup\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('tex ∪ \\sqcup', result.output)
        result = kurt.check_text('load set\nchain ⊂\n')
        self.assertFalse(result.ok)
        self.assertIn('subset', result.error or '')


if __name__ == '__main__':
    unittest.main()
