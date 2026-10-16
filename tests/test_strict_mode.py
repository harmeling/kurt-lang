import copy
import os
import tempfile
import unittest

import kurt.kurt as kurt   # the module itself, since `strict_mode` is a module-level setting


# `--strict` (for grading): `use`, `todo`, `chain` and `calc` bindings are only allowed in trusted theory files,
# i.e. the theories that come with Kurt, or the ones found via `-p`
class TestStrictMode(unittest.TestCase):
    def setUp(self):
        kurt.run_state.strict_mode = True
        self.trusted = list(kurt.run_state.trusted_paths)

    def tearDown(self):
        kurt.run_state.strict_mode = False
        kurt.run_state.trusted_paths[:] = self.trusted

    def check(self, source: str, tmp: str) -> None:
        path = os.path.join(tmp, 'exercise.kurt')
        with open(path, 'w') as fh:
            fh.write(source)
        kurt.load_file(path, copy.deepcopy(kurt.initial_kb), main=False)

    def test_rejects_unproven_statements(self):
        for source in ['bool A\nuse A\n', 'bool A\ntodo A\n', 'infix lt 20 20\nbool lt 0\nchain lt\n',
                       'infix plus 60 60\nbuiltin plus add\n',       # a `calc` binding is like an axiom
                       'infix plus 60 60\nsym plus\n', 'infix plus 60 60\nflat plus\n']:   # so are `sym` and `flat`
            with self.subTest(source=source), tempfile.TemporaryDirectory() as tmp:
                with self.assertRaises(kurt.KurtException):
                    self.check(source, tmp)

    def test_a_chain_needs_its_rules_proved_before_it(self):
        # todo 3 (2026-10-14; before, `chain` was refused with --strict): it generates no rules, each
        # of them must be a fact before it, and its notation uses them; a missing one is named
        with tempfile.TemporaryDirectory() as tmp:
            self.check('load natural\ninfix ≺ 20 20\ndef $x ≺ $y iff $x < $y   "prec"\nshow ($a ≺ $b) and ($b ≺ $c) implies ($a ≺ $c)\nproof\n    assume ($a ≺ $b) and ($b ≺ $c)\n        $a < $b\n        $b < $c\n        ($a < $b) and ($b < $c)\n        $a < $c\n        $a ≺ $c\nqed\nchain ≺\nconst p, q, r\nshow (p ≺ q) and (q ≺ r) implies p ≺ r\nproof\n    assume (p ≺ q) and (q ≺ r)\n        p ≺ q\n          ≺ r\nqed\n', tmp)
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaises(kurt.KurtException) as caught:      # `x R y` for `y = x + 1` isn't transitive
                self.check('load natural\ninfix R 20 20\ndef $x R $y iff $y = $x + 1\nchain R\n', tmp)
            self.assertIn('show ($a R $b) and ($b R $c) implies ($a R $c)', caught.exception.msg)

    def test_a_chain_has_at_most_three_operators(self):
        kurt.run_state.strict_mode = False
        result = kurt.check_text('infix a1 20 20, a2 20 20, a3 20 20, a4 20 20\nchain a1 a2 a3 a4\n')
        self.assertIn('at most three operators', result.error)

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
            kurt.run_state.trusted_paths.append(kurt.Path(teacher))
            search = kurt.run_state.theory_path[:]
            kurt.run_state.theory_path.insert(1, kurt.Path(teacher))
            try:
                self.check('load axioms\nP\n', tmp)
            finally:
                kurt.run_state.theory_path[:] = search


if __name__ == '__main__':
    unittest.main()
