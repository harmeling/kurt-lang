import os
import tempfile
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT

# a theory loads the theories whose symbols it uses: `∀` reached analysis.kurt via natural.kurt,
# and if natural.kurt stopped loading logic.kurt, analysis.kurt would break. A trusted theory
# notes such a symbol; for any file, `kurt --deps` lists them (2026-10-09)

THEORIES = PROJECT_ROOT / 'src' / 'kurt' / 'theories'


class TestDirectLoads(unittest.TestCase):
    def test_every_theory_loads_what_it_uses(self):
        for path in sorted(THEORIES.glob('*.kurt')):
            if path.name == kurt.CORE_FILE:
                continue
            with self.subTest(theory=path.name):
                result = kurt.check_file(str(path))
                self.assertTrue(result.ok, result.error)
                self.assertNotIn('; note:', result.output)

    def test_a_trusted_theory_gets_the_note_a_proof_not(self):
        with tempfile.TemporaryDirectory() as teacher, tempfile.TemporaryDirectory() as student:
            text = 'load numbers\nconst a\nuse a = 1 "a-one"\n'      # `=` is from equality.kurt
            for d in (teacher, student):
                with open(os.path.join(d, 'mine.kurt'), 'w') as f:
                    f.write(text)
            session = kurt.new_session(kurt.RunConfig(paths=(teacher,)))
            trusted = session.check_file(os.path.join(teacher, 'mine.kurt'))
            self.assertIn('; note: `=` comes from `equality.kurt`', trusted.output)
            untrusted = session.check_file(os.path.join(student, 'mine.kurt'))
            self.assertNotIn('; note:', untrusted.output)

    def test_deps_lists_them(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'p.kurt')
            with open(path, 'w') as f:
                f.write('load numbers\nconst a\nuse a = 1\n')
            report = kurt.dependencies_str(path)
            self.assertIn('equality.kurt: `=`', report)
            with open(path, 'w') as f:
                f.write('load equality, numbers\nconst a\nuse a = 1\n')
            self.assertIn('used without loading: nothing', kurt.dependencies_str(path))

if __name__ == '__main__':
    unittest.main()
