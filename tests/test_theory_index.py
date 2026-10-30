import copy
import contextlib
import io
import unittest
import unittest.mock

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

        with unittest.mock.patch.object(kurt.KnowledgeBase, 'theory_candidates', checked):
            for name in ['src/kurt/theories/group.kurt', 'src/kurt/theories/set.kurt',
                         'proofs/natural-deduction/contraposition.kurt', 'proofs/debug/conditional-rewriting.kurt',
                         'proofs/debug/cases-three-and-four.kurt', 'proofs/debug/calc-membership.kurt']:
                kb = copy.deepcopy(kurt.initial_kb)
                with contextlib.redirect_stdout(io.StringIO()):
                    kurt.load_file(str(PROJECT_ROOT / name), kb, main=True)
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
                cert, _ = kurt.impl_elim(goal, frozenset(kurt.free_bound_vars(goal, kb)[0]), f, '<test>', kurt.State.empty(), kb)
                self.assertIsNone(cert, f'{kurt.expr_str(formula, kb)} concludes {kurt.expr_str(goal, kb)}')
                skipped[0] += 1
            return answer

        with unittest.mock.patch.object(kurt, 'cannot_conclude', checked):
            for name in ['proofs/modal-logic/t-and-duality.kurt', 'proofs/natural-deduction/contraposition.kurt',
                         'proofs/debug/cases-three-and-four.kurt', 'proofs/debug/iff-true.kurt', 'src/kurt/theories/group.kurt']:
                kb = copy.deepcopy(kurt.initial_kb)
                with contextlib.redirect_stdout(io.StringIO()):
                    kurt.load_file(str(PROJECT_ROOT / name), kb, main=True)
        self.assertGreater(skipped[0], 1000)

    def test_the_heads_filter_rejects_only_what_cannot_unify(self):
        # `HeadsFilter` (before `cannot_unify` in `match_all_theory`, todo 50): every formula it
        # rejects, `cannot_unify` rejects too -- checked on every call
        original = kurt.HeadsFilter.rejects
        rejected = [0]

        def checked(self_, f):
            answer = original(self_, f)
            if answer:
                pattern = self_.pattern_expr
                self.assertTrue(kurt.cannot_unify(f.simplified_expr, pattern, self_.kb),
                                f'{kurt.expr_str(f.simplified_expr, self_.kb)} against {kurt.expr_str(pattern, self_.kb)}')
                rejected[0] += 1
            return answer

        with unittest.mock.patch.object(kurt.HeadsFilter, 'rejects', checked):
            for name in ['src/kurt/theories/group.kurt', 'src/kurt/theories/set.kurt', 'proofs/debug/conditional-rewriting.kurt',
                         'proofs/debug/cases-three-and-four.kurt', 'proofs/debug/calc-membership.kurt', 'proofs/linear-algebra/cauchy-schwarz.kurt']:
                kb = copy.deepcopy(kurt.initial_kb)
                with contextlib.redirect_stdout(io.StringIO()):
                    kurt.load_file(str(PROJECT_ROOT / name), kb, main=True)
        self.assertGreater(rejected[0], 1000)

    def test_a_hopeless_split_has_no_split_that_works(self):
        # `hopeless_split` (todo 50): when it says that no split of a disjunction's alternatives gives
        # the premises, the search without it finds none either -- checked on every call
        original = kurt.hopeless_split
        hopeless = [0]

        def checked(disjunction, pattern, tail, s, kb):
            answer = original(disjunction, pattern, tail, s, kb)
            if answer:
                for s_cand in kurt.unify_exprs_with_patterns([(disjunction, pattern)], s, kb):
                    rest = [kurt.apply_subst(e, s_cand, kb) for e in tail]
                    with unittest.mock.patch.object(kurt, 'hopeless_split', original):
                        found = kurt.match_all_theory(rest, s_cand, kb)[0]
                    self.assertFalse(found, f'{kurt.expr_str(disjunction, kb)} against {kurt.expr_str(pattern, kb)}')
                hopeless[0] += 1
            return answer

        with unittest.mock.patch.object(kurt, 'hopeless_split', checked):
            # (the alternatives D and E are each in one group, both with A: no exact cover, though every one is covered)
            for text in ['load propositional\nprop A, B, C, D, E, G\nuse A or B or C or D or E\nuse A implies G\nuse B implies G\nuse C implies G\n'
                         'use (A or D) implies G\nuse (A or E) implies G\nexpect "ProofError"\n    G\n',
                         'load propositional\nprop A, B, C, G\nuse A or B or C\nuse A implies G\nuse B implies G\nexpect "ProofError"\n    G\n',
                         # (premises with variables, 2026-10-24: `D ∧ %X` fits no alternative; the parts of `B ∨ (D ∧ %X)` each
                         # one alternative, so that `C` is in no group of two or three)
                         'load propositional\nprop A, B, C, D, G\nuse A or B or C or D\nuse A implies G\nuse B implies G\nuse C implies G\n'
                         'use (A or (D and %X)) implies G\nexpect "ProofError"\n    G\n',
                         'load propositional\nprop A, B, C, D, E, G\nuse A or B or (D and E) or C\nuse A implies G\n'
                         'use (B or (D and %X)) implies G\nexpect "ProofError"\n    G\n',
                         # (2026-10-25: the parts `D ∧ %X` and `E ∧ %X` together need `%X` to be `P` and `Q`;
                         # with `load logic`, "forall-elim" `(∀ $$x %A) ⇒ ...` whose binder fits no alternative)
                         'load propositional\nprop A, B, D, E, P, Q, G\nuse A or B or (D and P) or (E and Q)\nuse A implies G\n'
                         'use B implies G\nuse ((D and %X) or (E and %X)) implies G\nexpect "ProofError"\n    G\n',
                         'load logic\nprop A, B, C, D, G\nuse A or B or C or D\nuse A implies G\nuse B implies G\nuse C implies G\n'
                         'use (A or (forall y %X)) implies G\nexpect "ProofError"\n    G\n']:
                result = kurt.Session().check_text(text)
                self.assertTrue(result.ok, result.error)
            # (and where the part with a variable gives the group that is needed: proved)
            for text in ['load propositional\nprop A, B, C, D, E, G\nuse A or B or (D and E)\nuse A implies G\nuse (B or (D and %X)) implies G\nG\n',
                         'load propositional\nprop A, B, C, D, E, G\nuse A or B or C or (D and E)\nuse A implies G\nuse B implies G\n'
                         'use (C or (D and %X)) implies G\nG\n',
                         'load propositional\nprop A, B, C, D, E, G\nuse A or B or C or (D and E)\nuse A implies G\nuse B implies G\nuse C implies G\n'
                         'use (D and %X) implies G\nG\n',
                         # (`H ∨ %X` fits no group of the alternatives, though `%X` may be any group: `H` is none -- `G` by "excluded-middle")
                         'load propositional\nprop A, B, C, H, G\nuse A or B or C\nuse A implies G\nuse B implies G\nuse (H or %X) implies G\nG\n',
                         # (2026-10-25: `D ∧ %X` and `E ∧ %X` with one value, `P`; and a binder that is an alternative)
                         'load propositional\nprop A, B, D, E, P, G\nuse A or B or (D and P) or (E and P)\nuse A implies G\n'
                         'use B implies G\nuse ((D and %X) or (E and %X)) implies G\nG\n',
                         'load logic\nprop A, B, C, G\nprop P, Q\narity P 1\nuse A or B or C or (forall y (P(y) or Q))\nuse A implies G\n'
                         'use B implies G\nuse (C or (forall y (P(y) or %X))) implies G\nG\n']:
                result = kurt.Session().check_text(text)
                self.assertTrue(result.ok, result.error)
            kb = copy.deepcopy(kurt.initial_kb)
            with contextlib.redirect_stdout(io.StringIO()):
                kurt.load_file(str(PROJECT_ROOT / 'proofs/debug/cases-three-and-four.kurt'), kb, main=True)
        self.assertGreater(hopeless[0], 0)


    def test_a_pair_whose_tops_clash_does_not_unify(self):
        # `heads_clash` (todo 50, before each pair of `unify_in_any_order`): when it says that two
        # expressions can't unify by their tops, the unifier finds no match either, in the state of
        # the search -- checked on every pair (derivative-rules.kurt: `1` against `sub $x $a %F`, which
        # `match_against_sub` matches; a first version took them for a clash, as `cannot_unify` does)
        original = kurt.unify_in_any_order
        clashes = [0]

        def checked(tail_e, tail_p, tail, s, kb):
            if tail_p:
                p = s.walk(tail_p[0])
                for e in tail_e:
                    if kurt.heads_clash(s.walk(e), p, kb):
                        self.assertIsNone(next(kurt.unify_exprs_with_patterns([(e, tail_p[0])], s, kb), None),
                                          f'{kurt.expr_str(s.walk(e), kb)} against {kurt.expr_str(p, kb)}')
                        clashes[0] += 1
            yield from original(tail_e, tail_p, tail, s, kb)

        with unittest.mock.patch.object(kurt, 'unify_in_any_order', checked):
            for name in ['src/kurt/theories/group.kurt', 'proofs/natural-deduction/contraposition.kurt',
                         'proofs/debug/conditional-rewriting.kurt', 'proofs/debug/calc-membership.kurt',
                         'proofs/analysis/derivative-rules.kurt']:
                kb = copy.deepcopy(kurt.initial_kb)
                with contextlib.redirect_stdout(io.StringIO()):
                    kurt.load_file(str(PROJECT_ROOT / name), kb, main=True)
        self.assertGreater(clashes[0], 1000)

    def test_the_conditions_of_binders_are_checked_as_free_bound_vars_does(self):
        # `valid_binder_conditions` walks the binders itself since 2026-10-25 (todo 50; before, it was
        # `free_bound_vars`, which raises for a condition of the wrong shape): the same answer on every call
        original = kurt.valid_binder_conditions
        answers = {True: 0, False: 0}

        def reference(e, kb):
            try:
                kurt.free_bound_vars(e, kb)
                return True
            except kurt.KurtException:
                return False

        def checked(e, kb):
            answer = original(e, kb)
            self.assertEqual(answer, reference(e, kb), kurt.expr_str(e, kb))
            answers[answer] += 1
            return answer

        with unittest.mock.patch.object(kurt, 'valid_binder_conditions', checked):
            for name in ['src/kurt/theories/set.kurt', 'proofs/analysis/derivative-rules.kurt',
                         'proofs/soundness/conditioned-quantifier-rules.kurt', 'proofs/debug/quantifier-condition-not-a-subterm.kurt']:
                kb = copy.deepcopy(kurt.initial_kb)
                with contextlib.redirect_stdout(io.StringIO()):
                    kurt.load_file(str(PROJECT_ROOT / name), kb, main=True)
        self.assertGreater(answers[True], 1000)
        # (and a condition of the wrong shape, below other terms: a number where the variable goes)
        kb = copy.deepcopy(kurt.initial_kb)
        kb.add_arity('all', 2)
        kb.add_binder('all')
        sym, one = (lambda v: kurt.Token('SYMBOL', v)), kurt.Token('INT', '1')
        cases: list[kurt.Expr] = [[sym('all'), one, sym('P')], [sym('f'), sym('a'), [sym('all'), one, sym('P')]],
                                  [sym('all'), sym('y'), [sym('all'), one, sym('y')]], [sym('all'), sym('y'), [sym('f'), sym('y')]]]
        for e in cases:
            self.assertEqual(original(e, kb), reference(e, kb), kurt.expr_str(e, kb))
        self.assertFalse(original([sym('f'), sym('a'), [sym('all'), one, sym('P')]], kb))

    def test_no_bound_value_is_changed_in_place(self):
        # `State.bind` keeps the value itself, not a copy (todo 50): no expression is changed in place
        # once it is built, so a value shared with the expression it came from stays as it was -- each
        # value bound while files are checked, with its lists and tokens, compared at the end
        e: kurt.Expr = [kurt.Token('SYMBOL', 'f'), kurt.Token('SYMBOL', 'a')]
        self.assertIs(kurt.State.empty().bind('$x', e).lookup('$x'), e)

        def snapshot(x):
            if isinstance(x, list):
                return ('L', id(x), tuple(snapshot(c) for c in x))
            return ('T', id(x), x.label, x.value, x.column, x.origin, x.chained, x.glued)
        original = kurt.State.bind
        bound = []

        def checked(state, v, value):
            bound.append((value, snapshot(value)))
            return original(state, v, value)

        with unittest.mock.patch.object(kurt.State, 'bind', checked):
            for name in ['src/kurt/theories/group.kurt', 'proofs/natural-deduction/contraposition.kurt',
                         'proofs/debug/cases-three-and-four.kurt', 'proofs/debug/conditional-rewriting.kurt']:
                kb = copy.deepcopy(kurt.initial_kb)
                with contextlib.redirect_stdout(io.StringIO()):
                    kurt.load_file(str(PROJECT_ROOT / name), kb, main=True)
        self.assertGreater(len(bound), 10000)
        self.assertEqual([x for x, before in bound if snapshot(x) != before], [])

if __name__ == '__main__':
    unittest.main()
