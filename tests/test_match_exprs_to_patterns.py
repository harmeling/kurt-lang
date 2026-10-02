import unittest
import copy

from kurt import (
    Token, Expr, State,
    initial_kb,
    unify_exprs_with_patterns,
    trigger_sub
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
        # `forall`/`exists` are declared (arity + bindop) in `initial_kb` itself now,
        # no need to redeclare them here
        if hasattr(self.kb, "add_arity"):
            self.kb.add_arity("P", 1)
        # `=` just used as a plain 2-ary function symbol in these tests
        if hasattr(self.kb, "add_arity"):
            self.kb.add_arity("=", 2)
        if hasattr(self.kb, "add_bool"):
            self.kb.add_bool("=", [0])
            self.kb.add_bool("P", [0])

    # --- 1) plain one-sided matching ---
    def test_match_plain_var_on_pattern(self):
        # expr: f(1,0), pattern: f($x,0)  -> {$x -> 1}
        expr = app("f", num(1), num(0))
        pat  = app("f", sym("$x"), num(0))

        sols = list(unify_exprs_with_patterns([(expr, pat)], State.empty(), self.kb))
        self.assertEqual(len(sols), 1)
        self.assertTrue(sols[0].lookup("$x") == num(1))

    # --- 2) boolean variable on pattern ---
    def test_match_bool_var_on_pattern(self):
        # ensure %A is recognized as boolean var by your KB
        # most kurt setups treat symbols like "%A" as boolean schema vars out of the box
        expr = app("P", sym("a"))
        pat  = sym("%A")   # boolean variable

        sols = list(unify_exprs_with_patterns([(expr, pat)], State.empty(), self.kb))
        self.assertEqual(len(sols), 1)
        self.assertTrue(sols[0].lookup("%A") == expr)

    # --- 3) unification allows var on expr side ---
    def test_unify_var_on_expr_side(self):
        # unify: ($x, $y)  with unify_flag=True  → either bind pattern var first or expr var
        expr = sym("$x")
        pat  = sym("$y")

        sols = list(unify_exprs_with_patterns([(expr, pat)], State.empty(), self.kb))
        # Your code orients to the pattern var first → {$y: $x}
        self.assertEqual(len(sols), 1)
        self.assertTrue(sols[0].lookup("$y") == sym("$x"))

    # --- 4) occurs-check blocks infinite terms ---
    def test_unify_occurs_check_blocks(self):
        # unify: $x  with  f($x)  must fail due to occurs check
        expr = sym("$x")
        pat  = app("f", sym("$x"))

        sols = list(unify_exprs_with_patterns([(expr, pat)], State.empty(), self.kb))
        self.assertEqual(sols, [])

    # --- 5) binder matching with different bound names ---
    def test_match_binders_alpha_equivalence(self):
        # expr: forall $z. P($z)   vs pattern: forall $x. P($x)  → match succeeds (no subst needed)
        expr = forall("$z", app("P", sym("$z")))
        pat  = forall("$x", app("P", sym("$x")))

        sols = list(unify_exprs_with_patterns([(expr, pat)], State.empty(), self.kb))
        self.assertEqual(len(sols), 1)
        self.assertEqual(sols[0].subst, {})   # no free vars → empty substitution

    # --- 6) 'sub' special: match concrete expr against sub-pattern ---
    def test_match_against_sub_pattern(self):
        # Try to match expr (= b 0) against pattern (sub $x $a %A)
        # One valid solution: $a := b, %A := (= $x 0)
        expr = app("=", sym("b"), num(0))
        pat  = sub("$x", sym("$a"), sym("%A"))

        sols = list(unify_exprs_with_patterns([(expr, pat)], State.empty(), self.kb))
        # At least one solution with those bindings
        self.assertTrue(any(s.lookup("%A") == app("=", sym("$x"), num(0)) and s.lookup("$a") == sym("b") for s in sols))

    # --- 7) equal-expr short-circuit (after walk) ---
    def test_equal_short_circuit(self):
        # expr == pattern after applying existing σ → tail processed unchanged
        expr = app("f", sym("$x"))
        pat  = app("f", sym("$y"))
        s = State({"$y": sym("$x")}, frozenset(), frozenset())

        sols = list(unify_exprs_with_patterns([(expr, pat)], s, self.kb))
        # Should just propagate sigma; no new bindings needed
        self.assertEqual(len(sols), 1)
        self.assertEqual(sols[0].lookup("$y"), sym("$x"))

    # --- 8) blocked prevents capturing/binding to blocked symbol ---
    def test_blocked_prevents_binding(self):
        # (1) pattern var should NOT bind to a "blocked as range" symbol on expr side
        # (2) expr should NOT bind if it is a "blocked as domain" symbol on pattern side
        expr = sym("$z")
        pat  = sym("$x")
        s = State({}, frozenset({"$z"}), frozenset({"$z"}))   # $z is always blocked

        sols = list(unify_exprs_with_patterns([(expr, pat)], s, self.kb))
        self.assertEqual(sols, [])

    # --- 9) unification with simple compound terms ---
    def test_unify_compound(self):
        # unify: f($x, 0)  with  f(1, $y)   → {$x=1, $y=0}
        expr = app("f", sym("$x"), num(0))
        pat  = app("f", num(1), sym("$y"))
        s = State.empty()

        sols = list(unify_exprs_with_patterns([(expr, pat)], s, self.kb))
        self.assertEqual(len(sols), 1)
        s = sols[0]
        self.assertEqual(s.lookup("$x"), num(1))
        self.assertEqual(s.lookup("$y"), num(0))

    # --- 10) binder with free variable under the binder body ---
    def test_binder_with_free_var_in_body(self):
        # match: forall $z. Q($z, $u)  against  forall $x. Q($x, $v)
        # → should relate the free variables ($u) to ($v) via matching (pattern var $v binds to $u)
        expr = forall("$z", app("Q", sym("$z"), sym("$u")))
        pat  = forall("$x", app("Q", sym("$x"), sym("$v")))
        s = State.empty()

        sols = list(unify_exprs_with_patterns([(expr, pat)], s, self.kb))
        self.assertEqual(len(sols), 1)
        self.assertEqual(sols[0].lookup("$v"), sym("$u"))

    def test_exists_intro_matching_allows_blocked_in_schema(self):
        kb = copy.deepcopy(initial_kb)
        kb.add_arity('prime', 1)
        kb.add_bool('prime', [0])

        # goal: (exists z (prime z))
        goal = [Token('SYMBOL','exists'), Token('SYMBOL','$z'), [Token('SYMBOL','prime'), Token('SYMBOL','$z')]]

        # theory contains: prime 2
        fact: list[Expr] = [Token('SYMBOL','prime'), Token('STRING','2')]
        # pretend it's already in kb.theory, but here we only test the matcher on the rule itself

        # rule: (sub $x $a %A) ⇒ (exists $x %A)
        LHS: list[Expr] = [Token('SYMBOL','sub'), Token('SYMBOL','$x'), Token('SYMBOL','$a'), Token('SYMBOL','%A')]
        RHS: list[Expr] = [Token('SYMBOL','exists'), Token('SYMBOL','$x'), Token('SYMBOL','%A')]

        # First: match RHS with goal to get a σ that binds %A ≡ (prime $x) up to α
        sols = list(unify_exprs_with_patterns([(goal, RHS)], State.empty(), kb))
        assert len(sols) >= 1
        sigma = sols[0]  # e.g. { '%A' : [prime, $z] } with binders aligned later

        # Now instantiate LHS with σ, and check it can match the fact by picking $a = 2
        LHS_inst = trigger_sub(LHS, sigma, kb)[0]  # or apply_subst if you prefer
        # We expect to be able to match (sub $x $a %A) to 'prime 2', i.e. choose a=2 and A=prime $x
        sols2 = list(unify_exprs_with_patterns([(fact, LHS_inst)], sigma, kb))
        for s in sols2:
            t = s.lookup('$a')
            assert isinstance(t, Token) and t.value=='2'

if __name__ == "__main__":
    unittest.main()