import unittest
import copy

from kurt.kurt import (
    Token, Expr,
    initial_kb,
    bare_bool_schema_axiom_warning,
)

def sym(name: str) -> Token:
    return Token(label="SYMBOL", value=name)

def app(op: str, *args: Expr) -> Expr:
    return [sym(op), *args]

def forall(x: str, body: Expr) -> Expr:
    return [sym("forall"), sym(x), body]

class TestBareBoolSchemaWarning(unittest.TestCase):
    def setUp(self):
        self.kb = copy.deepcopy(initial_kb)

    def test_bare_var_warns(self):
        # use %A
        self.assertIsNotNone(bare_bool_schema_axiom_warning(sym("%A"), self.kb))

    def test_implies_with_unrelated_conclusion_warns(self):
        # use %A implies P
        expr = app("implies", sym("%A"), sym("P"))
        self.assertIsNotNone(bare_bool_schema_axiom_warning(expr, self.kb))

    def test_implies_with_var_in_conclusion_does_not_warn(self):
        # use %A implies (%A or %B)   -- legitimate or-intro shape
        expr = app("implies", sym("%A"), app("or", sym("%A"), sym("%B")))
        self.assertIsNone(bare_bool_schema_axiom_warning(expr, self.kb))

    def test_iff_definition_warns(self):
        # def p iff %A
        expr = app("iff", sym("p"), sym("%A"))
        self.assertIsNotNone(bare_bool_schema_axiom_warning(expr, self.kb))

    def test_iff_reflexive_does_not_warn(self):
        # use %A iff %A -- legitimate restatement shape
        expr = app("iff", sym("%A"), sym("%A"))
        self.assertIsNone(bare_bool_schema_axiom_warning(expr, self.kb))

    def test_explicit_forall_wrapping_still_warns(self):
        # use forall %A (%A implies P) -- an explicit forall doesn't change the effect
        expr = forall("%A", app("implies", sym("%A"), sym("P")))
        self.assertIsNotNone(bare_bool_schema_axiom_warning(expr, self.kb))

    def test_non_bool_var_premise_does_not_warn(self):
        # $x implies P -- $x is not boolean, so this isn't the same trap
        # (also not realistically a valid boolean premise, but the check itself
        # should not be fooled by a non-bool-prefixed premise regardless)
        expr = app("implies", sym("$x"), sym("P"))
        self.assertIsNone(bare_bool_schema_axiom_warning(expr, self.kb))

    def test_ordinary_axiom_does_not_warn(self):
        # and-elim: (%A and %B) implies %A -- premise isn't a bare var at all
        expr = app("implies", app("and", sym("%A"), sym("%B")), sym("%A"))
        self.assertIsNone(bare_bool_schema_axiom_warning(expr, self.kb))

if __name__ == "__main__":
    unittest.main()
