import unittest
from pathlib import Path

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

THEORIES = PROJECT_ROOT / 'src' / 'kurt' / 'theories'


class TestTrustedEditorTexts(unittest.TestCase):
    # an editor checks the text it shows, not the file: a text is never trusted -- but a theory of
    # the running Kurt, unchanged, is that theory (before 2026-10-20 every theory opened in an editor
    # was checked as a stranger's file: "the role `equivalence` ... only by a theory that comes with Kurt")

    def test_an_unchanged_theory_is_trusted(self):
        path = (THEORIES / 'propositional.kurt').resolve()
        result = kurt.check_text(path.read_text(encoding='utf-8'), name=str(path))
        self.assertTrue(result.ok, result.error)

    def test_a_changed_theory_is_not(self):
        path = (THEORIES / 'propositional.kurt').resolve()
        result = kurt.check_text(path.read_text(encoding='utf-8') + '\n; an edit\n', name=str(path))
        self.assertFalse(result.ok)
        self.assertIn('only be given by a theory that comes with Kurt', result.error or '')

    def test_the_same_text_elsewhere_is_not(self):
        text = (THEORIES / 'propositional.kurt').read_text(encoding='utf-8')
        result = kurt.check_text(text, name='/tmp/elsewhere/propositional.kurt')
        self.assertFalse(result.ok)

    def test_a_theory_open_in_the_editor_is_loaded_as_the_theory(self):
        # the other open documents are overlays: `set.kurt` open in a tab, a proof loads it
        path = (THEORIES / 'set.kurt').resolve()
        proof = 'load set\nconst a\na ∈ {a}\n'
        unchanged = kurt.Session(kurt.RunConfig(overlays=((str(path), path.read_text(encoding='utf-8')),)))
        self.assertTrue(unchanged.check_text(proof).ok, unchanged.check_text(proof).error)
        changed = kurt.Session(kurt.RunConfig(overlays=((str(path), path.read_text(encoding='utf-8') + '\n; an edit\n'),)))
        self.assertFalse(changed.check_text(proof).ok)


if __name__ == '__main__':
    unittest.main()
