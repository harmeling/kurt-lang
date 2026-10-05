import copy
import unittest

from kurt.kurt import Token, Expr, initial_kb, cannot_unify, SUB_SYMBOL

# `match_all_theory` skips a formula of the theory that `cannot_unify` with a premise -- only for
# speed, so `cannot_unify` must never say so for two expressions that do unify: a variable, an
# operator variable or a `sub` may match anything, and a `flat` or `sym` operator its arguments in
# any order


def sym(name: str) -> Token:
    return Token(label="SYMBOL", value=name)

def num(n: int) -> Token:
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
        self.assertTrue(cannot_unify(num(1), app("in", sym("a"), sym("K")), self.kb))

    def test_may_unify(self):
        a_in_K = app("in", sym("a"), sym("K"))
        self.assertFalse(cannot_unify(a_in_K, app("in", sym("a"), sym("K")), self.kb))
        self.assertFalse(cannot_unify(app("in", sym("$x"), sym("K")), a_in_K, self.kb))     # a variable
        self.assertFalse(cannot_unify(a_in_K, app("in", sym("$x"), sym("K")), self.kb))
        self.assertFalse(cannot_unify(sym("%A"), a_in_K, self.kb))                          # a boolean variable
        self.assertFalse(cannot_unify(app("plus", sym("a"), num(1)), app("plus", num(1), sym("a")), self.kb))   # `sym`
        self.assertFalse(cannot_unify(app("circ", sym("a"), sym("b")), app("plus", sym("a"), sym("b")), self.kb))   # an operator variable
        self.assertFalse(cannot_unify(app("plus", sym("a"), sym("b")), app("circ", sym("a"), sym("b")), self.kb))
        sub = [sym(SUB_SYMBOL), sym("$x"), sym("$a"), sym("%A")]                             # `sub` matches by substitution
        self.assertFalse(cannot_unify(sub, a_in_K, self.kb))
        self.assertFalse(cannot_unify(a_in_K, sub, self.kb))

if __name__ == '__main__':
    unittest.main()
