import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt


class TestDeclarationOrigins(unittest.TestCase):
    def test_each_property_lists_the_line_that_established_it(self):
        result = kurt.check_text(
            'infix rel 20 20\n'
            'use a rel b\n'
            'var x\n'
            'const\n'
            'var\n'
            'infix\n',
            name='/tmp/declarations.kurt',
        )

        self.assertTrue(result.ok, result.error)
        self.assertIn('const rel', result.output)
        self.assertIn('; level 1, declarations.kurt:2',
                      next(line for line in result.output.splitlines()
                           if line.startswith('const rel') and '; level' in line))
        self.assertIn('; level 1, declarations.kurt:3',
                      next(line for line in result.output.splitlines()
                           if line.startswith('var x') and '; level' in line))
        self.assertIn('; level 1, declarations.kurt:1',
                      next(line for line in result.output.splitlines() if line.startswith('infix rel')))

    def test_origins_survive_load(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            helper = directory / 'helper.kurt'
            helper.write_text('const C\nuse C "c"\n')
            main = directory / 'main.kurt'
            main.write_text(f'load "{helper}"\nconst\n')

            result = kurt.check_file(str(main))

        self.assertTrue(result.ok, result.error)
        line = next(line for line in result.output.splitlines() if line.startswith('const C'))
        self.assertIn('; level 1, helper.kurt:1', line)

    def test_same_basenames_are_disambiguated_with_paths(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            first, second = directory / 'one', directory / 'two'
            first.mkdir()
            second.mkdir()
            (first / 'shared.kurt').write_text('const A\nuse A "a"\n')
            (second / 'shared.kurt').write_text('const B\nuse B "b"\n')
            main = directory / 'main.kurt'
            main.write_text(
                f'load "{first / "shared.kurt"}"\n'
                f'load "{second / "shared.kurt"}"\n'
                'const\n'
            )

            result = kurt.check_file(str(main))

            self.assertTrue(result.ok, result.error)
            a_line = next(line for line in result.output.splitlines() if line.startswith('const A'))
            b_line = next(line for line in result.output.splitlines() if line.startswith('const B'))
            self.assertIn(f'{first / "shared.kurt"}:1', a_line)
            self.assertIn(f'{second / "shared.kurt"}:1', b_line)


if __name__ == '__main__':
    unittest.main()
