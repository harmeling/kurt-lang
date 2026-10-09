import copy
import contextlib
import io
import unittest

import kurt.kurt as kurt
from tests.utils import PROJECT_ROOT


class TestTheoryIndex(unittest.TestCase):
    # the index of the theory (`theory_candidates`) only leaves out formulas that `cannot_unify`
    # rejects anyway, and keeps the order of `all_theory`; the prefilter of the rules
    # (`cannot_conclude`) only skips what can't conclude the goal -- checked on every call while
    # files are checked (theories with operator variables, `sub`, numbers, blocks)

    def test_the_same_candidates_as_without_index(self):
        original = kurt.KnowledgeBase.theory_candidates
        calls = [0]

        def checked(kb, pattern):
            with_index = list(original(kb, pattern))
            without = [f for f in kb.all_theory() if kb.calc or not kurt.cannot_unify(f.simplified_expr, pattern, kb)]
            self.assertEqual([id(f) for f in with_index if kb.calc or not kurt.cannot_unify(f.simplified_expr, pattern, kb)],
                             [id(f) for f in without], kurt.expr_str(pattern, kb))
            calls[0] += 1
            return iter(with_index)

        kurt.KnowledgeBase.theory_candidates = checked
        try:
            for name in ['src/kurt/theories/group.kurt', 'src/kurt/theories/set.kurt',
                         'proofs/natural-deduction/contraposition.kurt', 'proofs/debug/conditional-rewriting.kurt',
                         'proofs/debug/cases-three-and-four.kurt', 'proofs/debug/calc-membership.kurt']:
                kb = copy.deepcopy(kurt.initial_kb)
                with contextlib.redirect_stdout(io.StringIO()):
                    kurt.load_file(str(PROJECT_ROOT / name), kb, main=True)
        finally:
            kurt.KnowledgeBase.theory_candidates = original
        self.assertGreater(calls[0], 1000)

    def test_the_prefilter_of_the_rules_skips_only_what_cant_conclude(self):
        # `cannot_conclude` (before `impl_elim` in `derive_expr`): for every formula it skips,
        # `impl_elim` finds nothing either (restatements, the directions of an `iff`, ...)
        original = kurt.cannot_conclude
        skipped = [0]

        def checked(formula, goal, kb):
            answer = original(formula, goal, kb)
            if answer:
                f = next(f for f in kb.all_theory() if f.simplified_expr is formula)
                cert, _ = kurt.impl_elim(goal, kurt.free_bound_vars(goal, kb)[0], f, '<test>', kurt.State.empty(), kb)
                self.assertIsNone(cert, f'{kurt.expr_str(formula, kb)} concludes {kurt.expr_str(goal, kb)}')
                skipped[0] += 1
            return answer

        kurt.cannot_conclude = checked
        try:
            for name in ['proofs/modal-logic/t-and-duality.kurt', 'proofs/natural-deduction/contraposition.kurt',
                         'proofs/debug/cases-three-and-four.kurt', 'proofs/debug/iff-true.kurt', 'src/kurt/theories/group.kurt']:
                kb = copy.deepcopy(kurt.initial_kb)
                with contextlib.redirect_stdout(io.StringIO()):
                    kurt.load_file(str(PROJECT_ROOT / name), kb, main=True)
        finally:
            kurt.cannot_conclude = original
        self.assertGreater(skipped[0], 1000)


if __name__ == '__main__':
    unittest.main()
