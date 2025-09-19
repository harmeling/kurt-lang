import unittest
import copy

from kurt import (
    Token, Expr, Subst,
    initial_kb,
    match_exprs_to_patterns,
    walk,
    apply_subst,
)

# Try to import your SUB symbol name; fall back to "sub"
try:
    from kurt import SUB_SYMBOL
except Exception:
    SUB_SYMBOL = "sub"

# ---------- helpers ----------
def sym(name: str) -> Token:
    return Token(label="SYMBOL", value=name)

def num(n: int) -> Token:
    return Token(label="INT", value=str(n))

def app(op: str, *args: Expr) -> Expr:
    return [sym(op), *args]

def forall(x: str, body: Expr) -> Expr:
    return [sym("forall"), sym(x), body]

def exists(x: str, body: Expr) -> Expr:
    return [sym("exists"), sym(x), body]

def sub(x: str, a: Expr, A: Expr) -> Expr:
    return [sym(SUB_SYMBOL), sym(x), a, A]


class TestMatchExprsToPatterns(unittest.TestCase):
    def setUp(self):
        # fresh KB each test; add minimal binders used below
        self.kb = copy.deepcopy(initial_kb)
        # Make sure these are recognized as binding operators/with arity 2 (if your KB needs it)
        if hasattr(self.kb, "add_arity"):
            self.kb.add_arity("forall", 2)
            self.kb.add_arity("exists", 2)
        if hasattr(self.kb, "add_bindop"):
            self.kb.add_bindop("forall")
            self.kb.add_bindop("exists")
        # `=` just used as a plain 2-ary function symbol in these tests
        if hasattr(self.kb, "add_arity"):
            self.kb.add_arity("=", 2)
        if hasattr(self.kb, "add_bool"):
            self.kb.add_bool("=", [0])

    # --- 1) plain one-sided matching ---
    def test_match_plain_var_on_pattern(self):
        # expr: f(1,0), pattern: f($x,0)  -> {$x -> 1}
        expr = app("f", num(1), num(0))
        pat  = app("f", sym("$x"), num(0))
        blocked = frozenset()
        unify_flag = False

        sols = list(match_exprs_to_patterns([(expr, pat)], {}, blocked, unify_flag, self.kb))
        self.assertEqual(len(sols), 1)
        self.assertIn("$x", sols[0])
        self.assertEqual(sols[0]["$x"], num(1))

    # --- 2) boolean variable on pattern ---
    def test_match_bool_var_on_pattern(self):
        # ensure %A is recognized as boolean var by your KB
        # most kurt setups treat symbols like "%A" as boolean schema vars out of the box
        expr = app("P", sym("a"))
        pat  = sym("%A")   # boolean variable
        blocked = frozenset()
        unify_flag = False

        sols = list(match_exprs_to_patterns([(expr, pat)], {}, blocked, unify_flag, self.kb))
        self.assertEqual(len(sols), 1)
        self.assertIn("%A", sols[0])
        self.assertEqual(sols[0]["%A"], expr)

    # --- 3) unification allows var on expr side ---
    def test_unify_var_on_expr_side(self):
        # unify: ($x, $y)  with unify_flag=True  → either bind pattern var first or expr var
        expr = sym("$x")
        pat  = sym("$y")
        blocked = frozenset()
        unify_flag = True

        sols = list(match_exprs_to_patterns([(expr, pat)], {}, blocked, unify_flag, self.kb))
        # Your code orients to the pattern var first → {$y: $x}
        self.assertEqual(len(sols), 1)
        self.assertIn("$y", sols[0])
        self.assertEqual(sols[0]["$y"], sym("$x"))

    # --- 4) occurs-check blocks infinite terms ---
    def test_unify_occurs_check_blocks(self):
        # unify: $x  with  f($x)  must fail due to occurs check
        expr = sym("$x")
        pat  = app("f", sym("$x"))
        blocked = frozenset()
        unify_flag = True

        sols = list(match_exprs_to_patterns([(expr, pat)], {}, blocked, unify_flag, self.kb))
        self.assertEqual(sols, [])

    # --- 5) binder matching with different bound names ---
    def test_match_binders_alpha_equivalence(self):
        # expr: forall $z. P($z)   vs pattern: forall $x. P($x)  → match succeeds (no subst needed)
        expr = forall("$z", app("P", sym("$z")))
        pat  = forall("$x", app("P", sym("$x")))
        blocked = frozenset()
        unify_flag = False

        sols = list(match_exprs_to_patterns([(expr, pat)], {}, blocked, unify_flag, self.kb))
        self.assertEqual(len(sols), 1)
        self.assertEqual(sols[0], {})   # no free vars → empty substitution

    # --- 6) 'sub' special: match concrete expr against sub-pattern ---
    def test_match_against_sub_pattern(self):
        # Try to match expr (= b 0) against pattern (sub $x $a %A)
        # One valid solution: $a := b, %A := (= $x 0)
        expr = app("=", sym("b"), num(0))
        pat  = sub("$x", sym("$a"), sym("%A"))
        blocked = frozenset()
        unify_flag = False

        sols = list(match_exprs_to_patterns([(expr, pat)], {}, blocked, unify_flag, self.kb))
        # At least one solution with those bindings
        self.assertTrue(any(
            (("%A" in s) and ("$a" in s)
             and s["$a"] == sym("b")
             and s["%A"] == app("=", sym("$x"), num(0)))
            for s in sols
        ))

    # --- 7) equal-expr short-circuit (after walk) ---
    def test_equal_short_circuit(self):
        # expr == pattern after applying existing σ → tail processed unchanged
        expr = app("f", sym("$x"))
        pat  = app("f", sym("$y"))
        sigma: Subst = {"$y": sym("$x")}  # so walk(pattern) == expr
        blocked = frozenset()
        unify_flag = False

        sols = list(match_exprs_to_patterns([(expr, pat)], sigma, blocked, unify_flag, self.kb))
        # Should just propagate sigma; no new bindings needed
        self.assertEqual(len(sols), 1)
        self.assertEqual(sols[0], sigma)

    # --- 8) blocked prevents capturing/binding to blocked symbol ---
    def test_blocked_prevents_binding(self):
        # pattern var should NOT bind to a blocked symbol on expr side
        expr = sym("$z")
        pat  = sym("$x")
        blocked = frozenset({"$z"})
        unify_flag = False

        sols = list(match_exprs_to_patterns([(expr, pat)], {}, blocked, unify_flag, self.kb))
        self.assertEqual(sols, [])

    # --- 9) unification with simple compound terms ---
    def test_unify_compound(self):
        # unify: f($x, 0)  with  f(1, $y)   → {$x=1, $y=0}
        expr = app("f", sym("$x"), num(0))
        pat  = app("f", num(1), sym("$y"))
        blocked = frozenset()
        unify_flag = True

        sols = list(match_exprs_to_patterns([(expr, pat)], {}, blocked, unify_flag, self.kb))
        self.assertEqual(len(sols), 1)
        s = sols[0]
        self.assertEqual(s.get("$x"), num(1))
        self.assertEqual(s.get("$y"), num(0))

    # --- 10) binder with free variable under the binder body ---
    def test_binder_with_free_var_in_body(self):
        # match: forall $z. Q($z, $u)  against  forall $x. Q($x, $v)
        # → should relate the free variables ($u) to ($v) via matching (pattern var $v binds to $u)
        expr = forall("$z", app("Q", sym("$z"), sym("$u")))
        pat  = forall("$x", app("Q", sym("$x"), sym("$v")))
        blocked = frozenset()
        unify_flag = False

        sols = list(match_exprs_to_patterns([(expr, pat)], {}, blocked, unify_flag, self.kb))
        self.assertEqual(len(sols), 1)
        self.assertIn("$v", sols[0])
        self.assertEqual(sols[0]["$v"], sym("$u"))


if __name__ == "__main__":
    unittest.main()