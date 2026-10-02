import unittest
import copy

from kurt import (
    Token, Expr,
    initial_kb,
    equal_expr,
)

def sym(name: str) -> Token:
    return Token(label="SYMBOL", value=name)

def app(op: str, *args: Expr) -> Expr:
    return [sym(op), *args]

def forall(x: str, body: Expr) -> Expr:
    return [sym("forall"), sym(x), body]

def exists(x: str, body: Expr) -> Expr:
    return [sym("exists"), sym(x), body]

class TestEqualExprAlpha(unittest.TestCase):
    def setUp(self):
        self.kb = copy.deepcopy(initial_kb)

    def test_identical_expressions_are_equal(self):
        e = app("R", sym("a"), sym("b"))
        self.assertTrue(equal_expr(e, e, self.kb))

    def test_differently_named_bound_variables_are_alpha_equal(self):
        # forall x (P x)  ==  forall y (P y)
        e1 = forall("x", app("P", sym("x")))
        e2 = forall("y", app("P", sym("y")))
        self.assertTrue(equal_expr(e1, e2, self.kb))

    def test_nested_binder_alpha_equal(self):
        # exists x (forall y (R x y))  ==  exists a (forall b (R a b))
        e1 = exists("x", forall("y", app("R", sym("x"), sym("y"))))
        e2 = exists("a", forall("b", app("R", sym("a"), sym("b"))))
        self.assertTrue(equal_expr(e1, e2, self.kb))

    def test_different_predicate_is_not_equal(self):
        e1 = forall("x", app("P", sym("x")))
        e2 = forall("y", app("Q", sym("y")))
        self.assertFalse(equal_expr(e1, e2, self.kb))

    def test_different_quantifier_is_not_equal(self):
        e1 = forall("x", app("P", sym("x")))
        e2 = exists("x", app("P", sym("x")))
        self.assertFalse(equal_expr(e1, e2, self.kb))

    def test_free_variable_must_match_literally(self):
        # forall y (R c y)  !=  forall y (R d y)  -- `c`/`d` are free, not bound here
        e1 = forall("y", app("R", sym("c"), sym("y")))
        e2 = forall("y", app("R", sym("d"), sym("y")))
        self.assertFalse(equal_expr(e1, e2, self.kb))

    def test_free_variable_matching_a_bound_name_is_not_confused(self):
        # forall y (R c y)  !=  R c y   (one has y bound, the other has y free)
        e1 = forall("y", app("R", sym("c"), sym("y")))
        e2 = app("R", sym("c"), sym("y"))
        self.assertFalse(equal_expr(e1, e2, self.kb))

    def test_shadowing_handled_correctly(self):
        # exists x (forall x (R x x))  ==  exists a (forall b (R b b))
        e1 = exists("x", forall("x", app("R", sym("x"), sym("x"))))
        e2 = exists("a", forall("b", app("R", sym("b"), sym("b"))))
        self.assertTrue(equal_expr(e1, e2, self.kb))

    def test_non_bindop_structural_equality_unaffected(self):
        e1 = app("and", sym("A"), sym("B"))
        e2 = app("and", sym("A"), sym("C"))
        self.assertFalse(equal_expr(e1, e2, self.kb))
        e3 = app("and", sym("A"), sym("B"))
        self.assertTrue(equal_expr(e1, e3, self.kb))

if __name__ == "__main__":
    unittest.main()
