# tests/test_exists_intro_and_blocked_sets.py

import unittest
import copy
from typing import Optional

from kurt.kurt import (
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

def exists(x: str, body: Expr) -> Expr:
    return [sym("exists"), sym(x), body]

def sub(x: str, a: Expr, A: Expr) -> Expr:
    return [sym(SUB_SYMBOL), sym(x), a, A]


class TestExistsIntroAndBlockedSets(unittest.TestCase):
    def setUp(self):
        # Fresh KB for each test; ensure required symbols are registered
        self.kb = copy.deepcopy(initial_kb)
        # `exists` is declared (arity + bindop) in `initial_kb` itself now, no need to
        # redeclare it here
        if hasattr(self.kb, "add_arity"):
            self.kb.add_arity("prime", 1)
            self.kb.add_arity("Q", 1)
        if hasattr(self.kb, "add_bool"):
            # treat these as boolean-level (formula) heads when needed
            self.kb.add_bool("prime", [0])
            self.kb.add_bool("Q", [0])

    # --- 1) End-to-end: ∃-intro with A=prime 2, D=∃z. prime z ---
    def test_exists_intro_prime(self):
        A: Expr = app("prime", num(2))                 # fact
        LHS: Expr = sub("$x", sym("$a"), sym("%A"))    # premise schematic
        RHS: Expr = [sym("exists"), sym("$x"), sym("%A")]  # conclusion schematic
        D: Expr = exists("$z", app("prime", sym("$z")))

        # Step 1: match RHS to goal D, with goal free vars rigid
        sols1 = list(unify_exprs_with_patterns([(D, RHS)], State.empty(), self.kb))
        self.assertTrue(len(sols1) >= 1)
        sigma1 = sols1[0]

        # The schema %A should now be some body equivalent to (prime $z) up to α
        body: Optional[Expr] = sigma1.lookup("%A")
        self.assertIsNotNone(body)
        # Don’t bind the bound var itself:
        self.assertIsNone(sigma1.lookup("$z"))

        # Reduce sub-macro after RHS match
        LHS_inst: Expr = trigger_sub(LHS, sigma1, self.kb)[0]
        # After trigger_sub, the bound name is consumed: sub $x $a (%A) → (%A)[$x := $a]
        # In our case this should be prime $a
        self.assertEqual(LHS_inst, app("prime", sym("$a")))

        # Step 2: unify instantiated premise with fact A (allow instantiating $a)
        sols2 = list(unify_exprs_with_patterns([(A, LHS_inst)], sigma1, self.kb))
        self.assertTrue(len(sols2) >= 1)
        sigma = sols2[0]

        # Check we picked the correct witness and never solved for $z
        self.assertEqual(sigma.lookup("$a"), num(2))
        self.assertIsNone(sigma.lookup("$z"))

    # --- 2) Rigid-goal vars may appear in substitution range (y -> z), but are not solved for ---
    def test_rigid_goal_var_allowed_in_range(self):
        expr = app("Q", sym("$z"))        # concrete goal-side term
        pat  = app("Q", sym("$y"))        # rule-side variable to be bound

        # $z is a rigid goal variable: forbid as domain, but allow it to appear in images
        s0 = State({}, frozenset({"$z"}), frozenset())  # blocked_as_domain={$z}, blocked_as_range=∅

        sols = list(unify_exprs_with_patterns([(expr, pat)], s0, self.kb))
        self.assertEqual(len(sols), 1)
        self.assertEqual(sols[0].lookup("$y"), sym("$z"))
        # and we never tried to bind $z itself
        self.assertIsNone(sols[0].lookup("$z"))

    # --- 3) Bound variables are untouchable & may not appear in substitution images ---
    def test_bound_var_disallowed_in_range(self):
        # Model a situation where $x is a bound (eigen)variable in scope.
        # Attempting to set $y := $x should be disallowed when $x ∈ blocked_as_range.
        expr = app("Q", sym("$x"))
        pat  = app("Q", sym("$y"))

        s0 = State({}, frozenset({"$x"}), frozenset({"$x"}))  # bound var blocks both domain and range
        sols = list(unify_exprs_with_patterns([(expr, pat)], s0, self.kb))
        self.assertEqual(sols, [])  # cannot leak the bound $x into a substitution image

    # --- 4) After trigger_sub, bound name is consumed and premise matches fact with witness ---
    def test_trigger_sub_consumes_binder_then_unifies_with_fact(self):
        # Goal and rule conclusion
        D: Expr   = exists("$z", app("prime", sym("$z")))
        RHS: Expr = [sym("exists"), sym("$x"), sym("%A")]  # ∃x. %A
        # Rule premise and fact
        LHS: Expr = sub("$x", sym("$a"), sym("%A"))
        fact: Expr = app("prime", num(2))

        # Match RHS to D
        sols1 = list(unify_exprs_with_patterns([(D, RHS)], State.empty(), self.kb))
        self.assertTrue(sols1)
        sigma1 = sols1[0]

        # Reduce SUB; check the bound symbol does not remain
        LHS_inst = trigger_sub(LHS, sigma1, self.kb)[0]
        self.assertEqual(LHS_inst, app("prime", sym("$a")))
        # Now unify with fact: should simply choose witness $a := 2
        sols2 = list(unify_exprs_with_patterns([(fact, LHS_inst)], sigma1, self.kb))
        self.assertTrue(sols2)
        self.assertEqual(sols2[0].lookup("$a"), num(2))

    # --- 5) Safety: occurs-check still active under ∃-intro piping ---
    def test_occurs_check_still_blocks(self):
        # Craft %A to be f($x) so that after SUB we’d need $a = f($a) to match g(f($a)) with g($a) — impossible.
        # Setup: D matches RHS yielding %A = g($x) (or similar), but premise becomes g($a),
        # then try to match expr g(f($a)) vs g($a) → would require $a := f($a) (should fail).
        # We simulate the second step directly.
        expr = app("g", app("f", sym("$a")))
        prem = app("g", sym("$a"))
        s0 = State.empty()

        sols = list(unify_exprs_with_patterns([(expr, prem)], s0, self.kb))
        self.assertEqual(sols, [])  # occurs-check should prevent $a = f($a)

    # --- 6) No accidental binding of goal variable during premise unification ---
    def test_goal_var_not_solved_in_premise_unify(self):
        # Set up a state where $z was the goal variable from step 1
        s0 = State({}, frozenset({"$z"}), frozenset())  # $z is rigid as domain only
        fact = app("prime", num(2))
        # Premise after SUB should be prime $a; unify should bind $a, not $z
        prem = app("prime", sym("$a"))

        sols = list(unify_exprs_with_patterns([(fact, prem)], s0, self.kb))
        self.assertTrue(sols)
        s = sols[0]
        self.assertEqual(s.lookup("$a"), num(2))
        self.assertIsNone(s.lookup("$z"))  # ensure we didn’t try to solve for $z

if __name__ == "__main__":
    unittest.main()