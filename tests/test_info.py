import unittest

import kurt.kurt as kurt


class TestInfo(unittest.TestCase):
    def test_info_shows_declaration_def_and_facts_mentioning_the_symbol(self):
        result = kurt.check_text(
            'load number\n'
            'calc on\n'
            'def four = 2 + 2\n'
            'four = 4\n'
            'info four\n'
        )
        self.assertTrue(result.ok, result.error)
        self.assertIn('const four', result.output)
        # what `info` printed (the lines 3 and 4 are in the output anyway, as checked)
        info = result.output.split('const four', 1)[1]
        self.assertIn('def four = (2 + 2)', info)
        self.assertIn('four = 4', info)

    def test_info_on_unknown_symbol_says_so(self):
        result = kurt.check_text('load number\ninfo nonexistent\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('nothing known about `nonexistent`', result.output)

    def test_info_requires_a_symbol(self):
        result = kurt.check_text('info\n')
        self.assertFalse(result.ok)
        self.assertIn('wrong arguments', result.error or '')

    def test_info_does_not_confuse_a_symbol_with_a_loaded_file_of_the_same_name(self):
        import tempfile
        from pathlib import Path

        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'four.kurt'
            path.write_text('prop FileMarker\nuse FileMarker "file-marker"\n', encoding='utf-8')
            result = kurt.check_text(
                f'load "{path}"\n'
                'load number\n'
                'calc on\n'
                'def four = 2 + 2\n'
                'four = 4\n'
                'info four\n'
            )
            self.assertTrue(result.ok, result.error)
            self.assertIn('const four', result.output)
            info = result.output.split('const four', 1)[1]        # (what `info` printed)
            self.assertIn('def four = (2 + 2)', info)
            self.assertNotIn('FileMarker', result.output)


if __name__ == '__main__':
    unittest.main()
