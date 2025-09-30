# test_sub_walk_capture.py
import unittest
import copy

from kurt import (
    Token, State, Expr,
    initial_kb,
    # your functions under test:
    trigger_sub,
    capture_avoiding_replace,
)

# Try to import your SUB symbol name; fall back to the common literal.
try:
    from kurt import SUB_SYMBOL
except Exception:
    SUB_SYMBOL = "sub"

# Small helpers to build common ASTs
def sym(name: str) -> Token:
    return Token(label="SYMBOL", value=name)

def num(n: int) -> Token:
    return Token(label="INT", value=str(n))

def is_var_tok(tok: Token, kb) -> bool:
    return (
        isinstance(tok, Token)
        and tok.label == "SYMBOL"
        and isinstance(tok.value, str)
        and (kb.is_var(tok.value) or kb.is_bool_var(tok.value))
    )

class TestWalk(unittest.TestCase):
    def setUp(self):
        self.kb = copy.deepcopy(initial_kb)
        self.kb.add_arity('forall', 2)
        self.kb.add_arity('exists', 2)
        self.kb.add_bindop('forall')
        self.kb.add_bindop('exists')

    def test_walk_chain_deref(self):
        # σ = { $x -> $y, $y -> 1 }
        s = State({"$x": sym("$y"), "$y": num(1)}, frozenset(), frozenset())
        out = s.walk(sym("$x"))
        self.assertIsInstance(out, Token)
        assert isinstance(out, Token)
        self.assertEqual(out.label, "INT")
        self.assertEqual(out.value, "1")

    def test_walk_respects_blocked_head(self):
        # σ = { $x -> $y, $y -> 1 }, blocked={$x}  ⇒ remains $x
        s = State({"$x": sym("$y"), "$y": num(1)}, frozenset({"$x"}), frozenset())
        out = s.walk(sym("$x"))
        self.assertEqual(out, sym("$x"))

    def test_walk_respects_blocked_tail(self):
        # blocked={$y} only: $x resolves to $y and then stops at blocked
        s = State({"$x": sym("$y"), "$y": num(1)}, frozenset({"$y"}), frozenset())
        out = s.walk(sym("$x"))
        self.assertEqual(out, sym("$y"))

    def test_walk_non_var_term_unchanged(self):
        term: Expr = [sym("f"), sym("$x"), num(0)]
        s = State({"$x": num(1)}, frozenset(), frozenset())
        # walk is head-only; lists that aren't variable heads stay as-is
        out = s.walk(term)
        self.assertEqual(out, term)


class TestTriggerSub(unittest.TestCase):
    def setUp(self):
        self.kb = copy.deepcopy(initial_kb)
        self.kb.add_arity('forall', 2)
        self.kb.add_arity('exists', 2)
        self.kb.add_bindop('forall')
        self.kb.add_bindop('exists')

    def test_simple_substitution(self):
        # (sub $x $b ($x = 0))  ==>  ($b = 0)
        expr = [sym(SUB_SYMBOL), sym("$x"), sym("$b"), [sym("="), sym("$x"), num(0)]]
        out = trigger_sub(expr, State.empty(), kb=self.kb)[0]
        self.assertEqual(out, [sym("="), sym("$b"), num(0)])

    def test_sub_does_not_fire_with_schema_A(self):
        # (sub $x $b %A) should *not* fire while %A is schematic (boolean schema var)
        expr: Expr = [sym(SUB_SYMBOL), sym("$x"), sym("$b"), sym("%A")]
        out = trigger_sub(expr, State.empty(), kb=self.kb)[0]
        # Stays as a sub node (possibly normalized), not replaced by body.
        self.assertIsInstance(out, list)
        assert isinstance(out, list)
        self.assertTrue(len(out) >= 4)
        self.assertEqual(out[0], sym(SUB_SYMBOL))

    def test_sub_respects_binder_hygiene(self):
        # (sub $x $b (forall $x (P $x)))  ==>  (forall $x (P $x))  (no change inside binder)
        expr: Expr = [sym(SUB_SYMBOL), sym("$x"), sym("$b"),
                [sym("forall"), sym("$x"), [sym("P"), sym("$x")]]]
        out = trigger_sub(expr, State.empty(), kb=self.kb)[0]
        self.assertEqual(out, [sym("forall"), sym("$x"), [sym("P"), sym("$x")]])

    def test_nested_subs(self):
        # (sub $x t (sub $x u (= $x 1)))
        # inner fires to (= u 1); outer sees no $x anymore → leaves it
        expr: Expr = [sym(SUB_SYMBOL), sym("$x"), sym("t"),
                  [sym(SUB_SYMBOL), sym("$x"), sym("u"), [sym("="), sym("$x"), num(1)]]]
        out = trigger_sub(expr, State.empty(), kb=self.kb)[0]
        self.assertEqual(out, [ sym("="), sym("u"), num(1) ])

    def test_sub_combined_with_sigma_application(self):
        # σ = { $b -> $y, $y -> 0 }, (sub $x $b (= $x $y)) → (= $y 0) after trigger
        s = State({"$b": sym("$y"), "$y": num(0)}, frozenset(), frozenset())
        expr: Expr = [sym(SUB_SYMBOL), sym("$x"), sym("$b"), [sym("="), sym("$x"), sym("$y")]]
        out = trigger_sub(expr, s, kb=self.kb)[0]
        self.assertEqual(out, [sym("="), num(0), num(0)])


class TestCaptureAvoidingReplace(unittest.TestCase):
    def setUp(self):
        self.kb = copy.deepcopy(initial_kb)
        self.kb.add_arity('forall', 2)
        self.kb.add_arity('exists', 2)
        self.kb.add_bindop('forall')
        self.kb.add_bindop('exists')

    def _decompose_forall(self, e):
        """Utility: ensure e is [forall, bv, body] and return (bv_token, body_expr)."""
        self.assertIsInstance(e, list)
        self.assertGreaterEqual(len(e), 3)
        self.assertEqual(e[0], sym("forall"))
        self.assertIsInstance(e[1], Token)
        return e[1], e[2]

    def test_avoids_capture_by_alpha_renaming(self):
        # A = (forall $y (P $x $y)), substitute x := $y  →  forall $y1. P $y $y1 (with $y1 fresh ≠ $y)
        A = [sym("forall"), sym("$y"), [sym("P"), sym("$x"), sym("$y")]]
        t = sym("$y")
        out = capture_avoiding_replace(A, "$x", t, State.empty(), self.kb)
        bv, body = self._decompose_forall(out)
        self.assertNotEqual(bv, sym("$y"))        # renamed
        # body should be [P, $y, <bv>]
        self.assertEqual(body[0], sym("P"))
        self.assertEqual(body[1], sym("$y"))
        self.assertEqual(body[2], bv)

    def test_no_alpha_needed_when_binder_not_in_FV_t(self):
        # A = (forall $z (P $x $z)), x := $y  →  forall $z. P $y $z
        A = [sym("forall"), sym("$z"), [sym("P"), sym("$x"), sym("$z")]]
        t = sym("$y")
        out = capture_avoiding_replace(A, "$x", t, State.empty(), self.kb)
        self.assertEqual(out, [sym("forall"), sym("$z"), [sym("P"), sym("$y"), sym("$z")]])

    def test_no_sub_below_binder_of_x(self):
        # x is bound by the binder; substitution should not enter
        A: Expr = [sym("forall"), sym("$x"), [sym("Q"), sym("$x")]]
        t: Expr = [sym("f"), sym("$a")]
        out = capture_avoiding_replace(A, "$x", t, State.empty(), self.kb)
        self.assertEqual(out, [sym("forall"), sym("$x"), [sym("Q"), sym("$x")]])

    def test_nested_binders_alpha_only_where_needed(self):
        # A = forall y. exists y. R(x,y) , x := y  →  forall y1. exists y2. R(y, y2)
        A = [sym("forall"), sym("$y"),
                [sym("exists"), sym("$y"),
                    [sym("R"), sym("$x"), sym("$y")]]]
        out = capture_avoiding_replace(A, "$x", sym("$y"), State.empty(), self.kb)

        # ∀ binder renamed
        self.assertIsInstance(out, list)
        assert isinstance(out, list)
        self.assertEqual(out[0], sym("forall"))
        outer_bv = out[1]
        self.assertIsInstance(outer_bv, Token)
        self.assertNotEqual(outer_bv, sym("$y"))  # outer renamed

        # inside: [exists, <inner_bv>, [R, $y, <inner_bv>]]
        outer_body = out[2]
        self.assertIsInstance(outer_body, list)
        assert isinstance(outer_body, list)
        self.assertEqual(outer_body[0], sym("exists"))
        inner_bv = outer_body[1]
        self.assertIsInstance(inner_bv, Token)
        self.assertNotEqual(inner_bv, sym("$y"))  # inner renamed too

        inner_body = outer_body[2]
        self.assertEqual(inner_body, [sym("R"), sym("$y"), inner_bv])

    def test_composition_with_trigger_sub(self):
        # Evaluate sub after replacement: (sub $x t A[x:=t]) is idempotent
        A: Expr = [sym("="), sym("$x"), num(0)]
        t: Expr = sym("$b")
        Axt = capture_avoiding_replace(A, "$x", t, State.empty(), self.kb)   # (= $b 0)
        expr: Expr = [sym(SUB_SYMBOL), sym("$x"), t, Axt]           # (sub $x $b (= $b 0))
        out = trigger_sub(expr, State.empty(), self.kb)[0]
        self.assertEqual(out, [sym("="), sym("$b"), num(0)])


if __name__ == "__main__":
    unittest.main()