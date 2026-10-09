import unittest
import copy

from kurt.kurt import (
    Token, Expr,
    initial_kb,
    check_expr_label,
    Formula,
    free_symbols,
)
from tests.utils import with_quantifiers

def sym(name: str) -> Token:
    return Token(label="SYMBOL", value=name)

def string(value: str) -> Token:
    return Token(label="STRING", value=value)

def app(op: str, *args: Expr) -> Expr:
    return [sym(op), *args]

def forall(x: str, body: Expr) -> Expr:
    return [sym("forall"), sym(x), body]

class TestCheckExprLabel(unittest.TestCase):
    def setUp(self):
        self.kb = with_quantifiers(copy.deepcopy(initial_kb))

    def test_bare_expression_no_label(self):
        expr = sym("P")
        tail, label, local = check_expr_label(expr, self.kb)
        self.assertEqual(label, "")
        self.assertFalse(local)

    def test_expression_with_plain_label(self):
        # parser shape for `P "foo"`: [STRING, P]
        expr = [string("foo"), sym("P")]
        tail, label, local = check_expr_label(expr, self.kb)
        self.assertEqual(label, "foo")
        self.assertFalse(local)
        self.assertEqual(tail, sym("P"))

    def test_expression_with_local_label(self):
        # parser shape for `P local "foo"`, from `local_led`: [local, STRING, P]
        expr = [sym("local"), string("foo"), sym("P")]
        tail, label, local = check_expr_label(expr, self.kb)
        self.assertEqual(label, "foo")
        self.assertTrue(local)
        self.assertEqual(tail, sym("P"))

class TestFormulaIsExported(unittest.TestCase):
    def make(self, label, local):
        return Formula(None, sym("P"), "", "1", "f.kurt", label, "reason", keyword="use", local=local)

    def test_labeled_not_local_is_exported(self):
        self.assertTrue(self.make("foo", False).is_exported())

    def test_unlabeled_is_not_exported(self):
        self.assertFalse(self.make("", False).is_exported())

    def test_labeled_but_local_is_not_exported(self):
        self.assertFalse(self.make("foo", True).is_exported())

    def test_unlabeled_and_local_is_not_exported(self):
        self.assertFalse(self.make("", True).is_exported())

class TestFreeSymbols(unittest.TestCase):
    def setUp(self):
        self.kb = with_quantifiers(copy.deepcopy(initial_kb))

    def test_simple_expression(self):
        expr = app("R", sym("a"), sym("b"))
        self.assertEqual(free_symbols(expr, self.kb), {"R", "a", "b"})

    def test_bound_variable_excluded(self):
        expr = forall("x", app("P", sym("x")))
        self.assertEqual(free_symbols(expr, self.kb), {"forall", "P"})

    def test_free_variable_with_same_name_as_bound_elsewhere(self):
        # forall x (P x) and (Q x) -- the second `x` is free (outside the forall's body)
        expr = app("and", forall("x", app("P", sym("x"))), app("Q", sym("x")))
        self.assertEqual(free_symbols(expr, self.kb), {"and", "forall", "P", "Q", "x"})

if __name__ == "__main__":
    unittest.main()
