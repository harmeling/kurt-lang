import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt


class TestList(unittest.TestCase):
    def test_lists_a_loaded_theory_by_stem_basename_and_category(self):
        result = kurt.check_text(
            'load natural\n'
            'list const natural\n'
            'list infix "natural.kurt"\n'
            'list theory natural\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('; retained content from natural.kurt', result.output)
        self.assertIn('const Nat', result.output)
        self.assertIn('natural.kurt:21', result.output)
        self.assertIn('infix ∣ 20 20', result.output)
        self.assertIn('use ', result.output)

    def test_list_source_shows_all_retained_kinds(self):
        result = kurt.check_text('load group\nlist group\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('infix ∘ 70 70', result.output)
        self.assertIn('const group', result.output)
        self.assertIn('group.kurt:', result.output)
        self.assertIn('def ', result.output)

    def test_group_exports_schematic_operator_syntax_but_not_its_local_variable_role(self):
        result = kurt.check_text(
            'load group\n'
            'list infix group\n'
            'list const group\n'
            'list var group\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('infix ∘ 70 70', result.output)
        self.assertNotIn('const ∘', result.output)
        self.assertNotIn('var ∘', result.output)

    def test_list_and_list_files_show_loaded_files(self):
        for command in ('list', 'list files'):
            with self.subTest(command=command):
                result = kurt.check_text(f'load prop\n{command}\n')
                self.assertTrue(result.ok, result.error)
                self.assertIn('load ', result.output)
                self.assertIn('prop.kurt', result.output)

    def test_unknown_and_ambiguous_sources_are_reported(self):
        unknown = kurt.check_text('load prop\nlist missing\n')
        self.assertFalse(unknown.ok)
        self.assertIn('is not a loaded file', unknown.error or '')

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for folder, symbol in (('one', 'A'), ('two', 'B')):
                path = root / folder
                path.mkdir()
                (path / 'shared.kurt').write_text(
                    f'bool {symbol}\nuse {symbol} "{symbol}"\n', encoding='utf-8')
            text = f'load {root / "one/shared.kurt"}, {root / "two/shared.kurt"}\nlist shared\n'
            ambiguous = kurt.check_text(text)
            self.assertFalse(ambiguous.ok)
            self.assertIn('names more than one loaded file', ambiguous.error or '')
            self.assertIn('use a path', ambiguous.error or '')

            exact = kurt.check_text(text.replace('list shared', f'list {root / "one/shared.kurt"}'))
            self.assertTrue(exact.ok, exact.error)
            self.assertIn(str(root / 'one/shared.kurt'), exact.output)


if __name__ == '__main__':
    unittest.main()
