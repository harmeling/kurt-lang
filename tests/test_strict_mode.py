import copy
import os
import tempfile
import unittest

import kurt.kurt as kurt   # the module itself, since `strict_mode` is a module-level setting


# `--strict` (for grading): `use`, `todo` and `chain` are only allowed in trusted theory files,
# i.e. the theories that come with Kurt, or the ones found via `-p`
class TestStrictMode(unittest.TestCase):
    def setUp(self):
        kurt.strict_mode = True
        self.trusted = list(kurt.trusted_paths)

    def tearDown(self):
        kurt.strict_mode = False
        kurt.trusted_paths[:] = self.trusted

    def check(self, source: str, tmp: str) -> None:
        path = os.path.join(tmp, 'exercise.kurt')
        with open(path, 'w') as fh:
            fh.write(source)
        kurt.load_file(path, copy.deepcopy(kurt.initial_kb), mainstream=False)

    def test_rejects_unproven_statements(self):
        for source in ['bool A\nuse A\n', 'bool A\ntodo A\n', 'infix lt 20 20\nbool lt 0\nchain lt\n']:
            with self.subTest(source=source), tempfile.TemporaryDirectory() as tmp:
                with self.assertRaises(kurt.KurtException):
                    self.check(source, tmp)

    def test_requires_declarations(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(kurt.KurtException):
                self.check('load prop\nB implies B\n', tmp)
        with tempfile.TemporaryDirectory() as tmp:
            self.check('load prop\nbool B\nB implies B\n', tmp)

    def test_accepts_proofs_from_packaged_theories(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.check('load prop\nbool A\nshow A implies A\nproof\n    assume A\n        A\ntrue\n', tmp)

    def test_use_in_sandbox_is_harmless(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.check('bool A\nsandbox\n    use A\ntrue\n', tmp)

    def test_trusts_theories_from_the_path(self):
        with tempfile.TemporaryDirectory() as tmp, tempfile.TemporaryDirectory() as teacher:
            with open(os.path.join(teacher, 'axioms.kurt'), 'w') as fh:
                fh.write('bool P\nuse P "p"\n')
            kurt.trusted_paths.append(kurt.Path(teacher))
            search = kurt.theory_path[:]
            kurt.theory_path.insert(1, kurt.Path(teacher))
            try:
                self.check('load axioms\nP\n', tmp)
            finally:
                kurt.theory_path[:] = search


if __name__ == '__main__':
    unittest.main()
