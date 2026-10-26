import copy
import unittest

from kurt.kurt import Token, Expr, State, initial_kb, cannot_unify, unify_exprs_with_patterns, expr_str, SUB_SYMBOL

# `match_all_theory` skips a formula of the theory that `cannot_unify` with a premise -- only for
# speed, so `cannot_unify` must never say so for two expressions that do unify: a variable, an
# operator variable or a `sub` may match anything, and a `flat` or `sym` operator its arguments in
# any order


def sym(name: str) -> Token:
    return Token(label="SYMBOL", value=name)

def real(n: int) -> Token:
    return Token(label="INT", value=str(n))

def app(op: str, *args: Expr) -> Expr:
    return [sym(op), *args]


class TestCannotUnify(unittest.TestCase):
    def setUp(self):
        self.kb = copy.deepcopy(initial_kb)
        self.kb.add_infix("plus", 60, 60)
        self.kb.add_flat("plus")
        self.kb.add_sym("plus")
        self.kb.add_var("circ")          # an operator variable, like the `∘` of group.kurt

    def test_different_constants_or_operators(self):
        self.assertTrue(cannot_unify(app("in", sym("a"), sym("K")), app("in", sym("a"), sym("V")), self.kb))
        self.assertTrue(cannot_unify(app("in", sym("a"), sym("K")), app("eq", sym("a"), sym("K")), self.kb))
        self.assertTrue(cannot_unify(sym("a"), sym("b"), self.kb))
        self.assertTrue(cannot_unify(real(1), app("in", sym("a"), sym("K")), self.kb))

    def test_may_unify(self):
        a_in_K = app("in", sym("a"), sym("K"))
        self.assertFalse(cannot_unify(a_in_K, app("in", sym("a"), sym("K")), self.kb))
        self.assertFalse(cannot_unify(app("in", sym("$x"), sym("K")), a_in_K, self.kb))     # a variable
        self.assertFalse(cannot_unify(a_in_K, app("in", sym("$x"), sym("K")), self.kb))
        self.assertFalse(cannot_unify(sym("%A"), a_in_K, self.kb))                          # a boolean variable
        self.assertFalse(cannot_unify(app("plus", sym("a"), real(1)), app("plus", real(1), sym("a")), self.kb))   # `sym`
        self.assertFalse(cannot_unify(app("circ", sym("a"), sym("b")), app("plus", sym("a"), sym("b")), self.kb))   # an operator variable
        self.assertFalse(cannot_unify(app("plus", sym("a"), sym("b")), app("circ", sym("a"), sym("b")), self.kb))
        sub: Expr = [sym(SUB_SYMBOL), sym("$x"), sym("$a"), sym("%A")]                             # `sub` matches by substitution
        self.assertFalse(cannot_unify(sub, a_in_K, self.kb))
        self.assertFalse(cannot_unify(a_in_K, sub, self.kb))

    def test_a_constant_symbol_against_a_term(self):
        # a plain symbol `G` unifies with no term with a constant operator -- the premise `Ai` of
        # `Ai ∧ K ⇒ G` was tried against every `Bj ∨ Cj` of the theory (2026-10-16)
        a_in_K = app("in", sym("a"), sym("K"))
        self.assertTrue(cannot_unify(sym("G"), a_in_K, self.kb))
        self.assertTrue(cannot_unify(a_in_K, sym("G"), self.kb))
        self.assertTrue(cannot_unify(sym("G"), app("plus", sym("a"), sym("b")), self.kb))    # also `flat`/`sym`
        self.assertFalse(cannot_unify(sym("$x"), a_in_K, self.kb))                           # a variable
        self.assertFalse(cannot_unify(sym("G"), app("circ", sym("a"), sym("b")), self.kb))   # an operator variable
        self.assertFalse(cannot_unify(sym("G"), [sym(SUB_SYMBOL), sym("$x"), sym("$a"), sym("%A")], self.kb))   # `sub`

    def test_below_a_symmetric_operator(self):
        # `=` is `sym` but not `flat`: the two arguments are matched in either order, so each one
        # needs a partner it may unify with (2026-10-16; before, nothing below `sym` was checked)
        self.kb.add_infix("eq", 20, 20)
        self.kb.add_sym("eq")
        f_b = app("f", sym("b"))
        self.assertTrue(cannot_unify(app("eq", sym("a"), f_b), app("eq", sym("c"), sym("d")), self.kb))      # `a` fits neither
        self.assertTrue(cannot_unify(app("eq", sym("$x"), sym("b")), app("eq", sym("c"), sym("d")), self.kb))  # `b` fits neither
        self.assertFalse(cannot_unify(app("eq", sym("a"), sym("b")), app("eq", sym("b"), sym("a")), self.kb))  # swapped
        self.assertFalse(cannot_unify(app("eq", sym("$x"), f_b), app("eq", sym("c"), app("f", sym("$y"))), self.kb))
        self.assertFalse(cannot_unify(app("eq", sym("$x"), sym("$y")), app("eq", sym("c"), f_b), self.kb))
        self.assertFalse(cannot_unify(app("plus", sym("a"), sym("$x")), app("plus", sym("c"), sym("d"), sym("a")), self.kb))  # `flat`: groups

    def test_below_a_flat_operator(self):
        # todo 50 (2026-10-23): with rigid arguments only on both sides -- constants, terms with a
        # constant operator -- a `flat` operator has as many on each side, each with a partner (`sym`) or
        # in the same place; an argument with the operator itself counts with its own arguments. A
        # false goal after a 9-way disjunction matched `A7 ∨ A7 ∨ A7 ∨ A7` against it in every grouping
        self.kb.add_infix("seq", 60, 60)
        self.kb.add_flat("seq")                                  # flat, not sym
        self.assertTrue(cannot_unify(app("plus", sym("a"), sym("b")), app("plus", sym("c"), sym("d")), self.kb))
        self.assertTrue(cannot_unify(app("plus", sym("a"), sym("b"), sym("c")), app("plus", sym("a"), sym("b")), self.kb))   # 3 against 2
        self.assertTrue(cannot_unify(app("plus", sym("a"), sym("a"), sym("a")), app("plus", sym("a"), sym("b"), sym("c")), self.kb))  # `b` has no partner
        self.assertTrue(cannot_unify(app("plus", app("plus", sym("a"), sym("a")), app("plus", sym("a"), sym("a"))),
                                     app("plus", sym("a"), sym("b"), sym("c"), sym("d")), self.kb))                              # nested, as flattened
        self.assertTrue(cannot_unify(app("seq", sym("a"), sym("b")), app("seq", sym("b"), sym("a")), self.kb))                  # not `sym`: in order
        self.assertFalse(cannot_unify(app("plus", sym("a"), sym("b")), app("plus", sym("b"), sym("a")), self.kb))               # `sym`
        self.assertFalse(cannot_unify(app("plus", sym("a"), app("f", sym("$y"))), app("plus", app("f", sym("c")), sym("a")), self.kb))
        self.assertFalse(cannot_unify(app("plus", sym("a"), sym("%A")), app("plus", sym("a"), sym("b"), sym("c")), self.kb))    # a variable: a group
        self.assertFalse(cannot_unify(app("plus", sym("a"), app("circ", sym("b"))), app("plus", sym("a"), sym("b"), sym("c")), self.kb))  # an operator variable
        sub: Expr = [sym(SUB_SYMBOL), sym("$x"), sym("$a"), sym("%A")]
        self.assertFalse(cannot_unify(app("plus", sym("a"), sub), app("plus", sym("a"), sym("b"), sym("c")), self.kb))          # `sub`

    def test_a_number_against_a_sub_term(self):
        # `match_against_sub` matches `1` with `sub y 1 y` -- before 2026-10-25 `cannot_unify` took a
        # number or a string against a `sub` term for a clash, and `cannot_conclude` skipped "sum-one"
        # for `(sum i (1, 1) i) = 1` (proofs/debug/number-against-sub.kurt, todo 50)
        sub: Expr = [sym(SUB_SYMBOL), sym("$x"), sym("$a"), sym("$T")]
        for token in (real(1), Token(label="STRING", value="s"), sym("a")):
            self.assertFalse(cannot_unify(token, sub, self.kb))
            self.assertFalse(cannot_unify(sub, token, self.kb))
            self.assertFalse(cannot_unify(app("f", token), app("f", sub), self.kb))
            self.assertFalse(cannot_unify(token, app("circ", sym("b")), self.kb))      # an operator variable
            self.assertTrue(cannot_unify(token, app("f", sym("b")), self.kb))

    def test_every_clash_fails_in_the_unifier(self):
        # every pair of small terms that `cannot_unify` rules out (both ways) has no unifier: constants,
        # numbers, strings, variables, a `flat`+`sym`, a `sym` and a plain operator, an operator
        # variable, a binder and `sub` terms (the case of 2026-10-25: a number against `sub`)
        self.kb.add_infix("eq", 20, 20)
        self.kb.add_sym("eq")
        self.kb.add_arity("all", 2)
        self.kb.add_bindop("all")
        leaves: list[Expr] = [sym("a"), sym("b"), real(1), real(2), Token(label="STRING", value="s"), sym("$x"), sym("$y")]
        def terms(depth: int) -> list[Expr]:
            if depth == 0:
                return list(leaves)
            smaller = terms(depth - 1)
            few = smaller[:5] + [t for t in smaller if isinstance(t, list)][:4]
            result = list(smaller)
            for t in few:
                result.append(app("f", t))
                result.append(app("circ", t))
                result.append([sym(SUB_SYMBOL), sym("$v"), t, sym("$v")])
                result.append([sym(SUB_SYMBOL), sym("$v"), sym("$a"), t])
                result.append(app("all", sym("z"), app("f", sym("z")) if t == sym("a") else t))
                for u in few[:4]:
                    result.append(app("plus", t, u))
                    result.append(app("eq", t, u))
                    result.append(app("g", t, u))
            return result
        all_terms = terms(2)
        clashes = 0
        for e in all_terms:
            for p in all_terms:
                if cannot_unify(e, p, self.kb):
                    clashes += 1
                    with self.subTest(e=expr_str(e, self.kb), p=expr_str(p, self.kb)):
                        self.assertEqual(next(unify_exprs_with_patterns([(e, p)], State.empty(), self.kb), None), None)
        self.assertGreater(clashes, 1000)


if __name__ == '__main__':
    unittest.main()
