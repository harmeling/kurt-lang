# Kurt soundness notes

**Scope.** This is not a formal soundness proof of Kurt. It is a working
audit: for each rule Kurt actually implements, what property it is supposed
to guarantee, where in `kurt.py` that's enforced, how well-tested that
enforcement is, and — where I found one — a bug that was fixed while
writing this. Read together with `proofs/soundness/`, which holds the
adversarial regression tests this audit produced: proof attempts that
*should* be rejected (or, for the false-rejection bug below, should now be
*accepted*), kept as permanent regression tests via the normal
`tests/test_kurt_proofs.py` discovery.

The goal this serves: "if Kurt says a proof is fine, it must be fine."
Everything below is about *soundness* (never accepting an invalid proof),
not completeness (finding every valid one) — the performance/multi-hop
items in `todo-claude.md` are a different, lower-stakes concern by
comparison.

## 1. What's genuinely hard-coded

`derive_expr`/`eval_expression` implement four rules directly in Python,
not as removable `use` axioms: `top-intro` (`true` is always derivable),
`impl-elim`/modus ponens (search `kb.all_theory()` for a matching
implication), `and-intro` (split/join conjunctions), and `not-intro`/
`impl-intro` as the effect of closing an `assume` block (§2). These are
simple enough that their correctness rests mostly on `impl_elim`'s
unification being correct (§3) rather than on rule-specific side
conditions.

`src/kurt/theories/minimal.kurt` (never actually loadable — it starts with
`false` on purpose) used to describe two *additional* hard-coded rules,
`"restatement"` (`$A implies $A`) and a generalized `"impl-intro"` schema,
that turned out not to exist: a bare `A implies A` does not derive from
nothing. Fixed by rewriting `minimal.kurt`'s inference-rules section to
describe only what's real, with an explicit note about what was removed
and why (see `todo-claude.md`). This was a documentation bug, not a
soundness one — but a wrong description of the trust boundary is exactly
the kind of thing that erodes confidence in what "if Kurt says it's fine"
actually covers, so it's included here.

## 2. Block-closing rules: `assume`/`let`/`pick`

These three (plus `case`, identical to `assume`) are where natural
deduction's classic soundness side-conditions live, and where I spent most
of the audit. All three are implemented in `eval_done` (§9 of
`kurt-doc.md` covers the user-facing behavior).

**`assume`/`case` → impl-intro / not-intro.** Assuming `P`, deriving `Q`,
gives `P implies Q`; deriving `false` additionally gives `not P`. No fresh
individual is introduced, so the interesting side condition (below) rarely
bites for plain `assume` — but it shares the same closing code path as
`let`/`pick`, so it's covered by the same check.

**`let` → forall-intro.** The classic side condition: generalizing over a
fresh constant `x` is only sound if `x` does not occur free in anything
still assumed outside the block — otherwise you've "proven" `forall x,
P(x)` when really you only showed it for whichever `x` happens to satisfy
the outer assumption, not for an arbitrary one.

**`pick` → exists-elim.** The dual condition: given `exists x, P(x)`, you
may name a witness and reason from `P(witness)`, but the witness (and
anything else local to that reasoning) must not appear in whatever you
conclude — otherwise the conclusion secretly depends on which witness you
happened to pick, defeating the point of not needing to know that.

**How it's enforced.** Both conditions reduce to the same check in
`eval_done`, after the mode-specific rule fires: `not_allowed` is computed
as "every constant registered at this level, except vocabulary symbols
(§2.1) and anything that's also a variable on the parent level", and
`contains(expr, not_allowed, kb_parent)` rejects the close if any of them
appear free (not bound) in the outgoing conclusion. `contains` is bound-
variable-aware — it stops "seeing" a symbol once it's inside a binder that
quantifies it (`x` inside `forall x (...)`) — which is what lets `let`
reuse the same constant name as the resulting `forall`'s bound variable
without `x` itself tripping the check. `pick` additionally has its own,
earlier, `pick`-specific version of the same check (`kb.const` filtered the
same way) before this shared one even runs.

Verified with adversarial tests (`proofs/soundness/`):
- `forall-intro-rejects-leaked-constant.kurt` — a `const helper` declared
  inside `let x`, referenced in the conclusion, correctly rejected.
- `exists-elim-rejects-leaked-constant.kurt` — same, for `pick`.

### 2.1 Bug found and fixed: vocabulary symbols were wrongly scoped

The check above uses `kb.const` — every symbol *first registered as a
constant at this level* — as its starting point for "must not leak". But a
symbol only gets explicitly classified when it's actually *used* in an
expression (declaring `bool P`/`arity P 1` alone doesn't register it; the
first `use`/claim that mentions `P` does) — so if a predicate, function, or
plain boolean proposition happens to be used for the very first time
*inside* a `let`/`pick` block, it was being registered as a constant of
*that level*, indistinguishable from a genuinely fresh individual like
`let`'s own bound variable or a bystander `const`. The check then wrongly
forbade it from appearing in the conclusion at all — rejecting perfectly
valid proofs like:

    load logic
    bool P
    arity P 1
    let x
        use P x
        P x
    ; forall x P x -- REJECTED before the fix, just because `P` was first
    ; used here, even though nothing about it depends on `x`'s freshness

This is a false-*rejection* bug (over-conservative), not a soundness hole —
but it directly undermines "let/pick are usable for real proofs", and it
was found by exactly the adversarial-testing process this audit is doing,
so it's recorded here rather than filed separately.

**Fix:** added `KnowledgeBase.is_vocabulary_symbol(s)` — true if `s` has
arity > 0, is a declared operator (`infix`/`prefix`/`postfix`/`brackets`),
is a `bindop`, or is declared `bool` — and excluded vocabulary symbols from
`not_allowed` in both the shared check and `pick`'s own earlier one.

**Why this doesn't reopen the hole it's excluding from:** the thing that
actually must not leak is the block's *own* fresh individual(s) (`let`'s
bound variable, `pick`'s witness) — and those remain fully protected
regardless of this exemption, because `contains`'s bound-variable exclusion
(not the vocabulary exemption) is what correctly keeps them scoped to their
own binder. The exemption only affects *other*, incidental symbols a proof
happens to mention for the first time inside the block. And even in the
most permissive remaining case — a function/operator symbol *invented*
fresh inside the block (e.g. `arity f 1` declared inside `let x`, then used
and escaped) — nothing is actually smuggled out: `pop_level` (unlike
`merge_and_pop`, used for `load`) does not merge syntax tables into the
parent at all, so `f`'s `arity` declaration is gone the moment the block
closes; only the already-fully-parsed formula survives, as plain data. I
did not find a way to turn that into an accepted false proof; see
`proofs/soundness/forall-intro-vocabulary-not-scoped.kurt` and
`exists-elim-vocabulary-not-scoped.kurt` for the confirming regression
tests (these must now *pass*, unlike the two leak tests above).

**A related, unaffected wrinkle:** `let`'s forall-wrapping always uses the
literal symbol `forall`, regardless of whether the current theory has
declared `forall` a `bindop` (e.g. via `load logic`). If it hasn't, the
generated term isn't recognized as a real binder anywhere downstream
(`contains`, matching, ...), and the *same* leak-check ends up rejecting
even a correct `let x` block with a confusing message, since `x` no longer
reads as bound. This is a footgun, not a soundness gap (the safe direction
— reject — is what happens), so it's noted here rather than fixed: using
`let` for genuine forall-intro requires `load logic` (or an equivalent
`bindop forall` declaration) first, same as it always has.

## 3. Capture-avoiding substitution

The `sub $x $a %A` operator, and everything built on it (`forall-elim`,
`exists-intro`, `equal-elim`, ...), depends on substitution never letting a
free variable get captured by a binder it substitutes into — the other
classical soundness pitfall, e.g. naively substituting `$x := y` into
`forall y (P $x y)` must not silently become `forall y (P y y)`.

This is covered by `capture_avoiding_replace` (and `trigger_sub`, which
routes through it), with focused unit tests
(`tests/test_sub_walk_capture.py`) that hit the exact textbook scenario:
`test_avoids_capture_by_alpha_renaming` substitutes `$x := $y` into
`forall $y (P $x $y)` and asserts the bound `$y` gets alpha-renamed rather
than capturing the substituted one; `test_no_alpha_needed_when_binder_not_in_FV_t`
and `test_nested_binders_alpha_only_where_needed` check the mechanism
doesn't rename *unnecessarily* either (which would just be noise, not a
soundness issue, but worth having pinned down); `test_sub_respects_binder_hygiene`
and `test_no_sub_below_binder_of_x` round it out.

**Not yet done:** all of the above tests exercise `capture_avoiding_replace`
directly, as a unit — I did not construct a full end-to-end `.kurt` proof
attempt that tries to exploit capture through an actual `forall-elim`/
`equal-elim` derivation and confirm it's still rejected/renamed correctly
at that level. Given how directly the proof-level code routes through the
tested primitives, I'd treat this as a good next increment rather than an
open red flag — see `todo-claude.md`.

## 4. Const/var exclusivity

Once a symbol is `const` or `var` on a level, it can't become the other —
checked in `add_const`/`add_var` (`EvalError` either direction). This is
what structurally prevents a more exotic version of the §2 leak: you can't
`let x` (which requires `x` to be a genuinely new symbol) using a name
that's already been used anywhere as an ordinary variable or constant, so a
fresh individual can never quietly alias something already meaningful
elsewhere. Already covered by existing regression tests
(`proofs/debug/const-const.kurt`, `const-var.kurt`, `var-const.kurt`,
`var-level-const.kurt`) — no new tests needed here.

## 5. Guard against silently losing these checks

Several of the checks above (and plenty of internal invariants elsewhere:
occurs-checks, level-stack bookkeeping, ...) are plain Python `assert`s
(`BUG:` messages) rather than `raise KurtException` — appropriate, since
they're "can't happen" invariants, not user-facing errors. But `python
-O`/`-OO` strips all `assert`s at compile time, which would silently
disable them. `main()` now refuses to run at all under `-O`/`-OO`
(`if not __debug__: ... sys.exit(1)`), so this can't happen unnoticed.

## 6. Open questions, not resolved here

- **Mixed boolean/non-boolean variables in one `let` list**
  (`let x, %A`) — `eval_done`'s forall-wrapping loop skips wrapping for
  conditions where `is_bool_var_token` is true, treating boolean-schema
  variables differently from ordinary ones. `todo.md` already flags this
  ("check that in forall_intro the quantification either applies to
  boolean or non-boolean vars, but not both") as unverified; I didn't
  construct a conclusive test either way in this pass.
- **`case` exhaustiveness** — nothing checks that a sequence of `case`
  blocks actually covers a real disjunction before the implicit `or-elim`
  step; a missing case just means the final combining claim fails to
  derive (a completeness gap, not a soundness one, since or-elim itself
  still requires the real `%A or %B` axiom to be in scope) — mentioned for
  completeness, not because it looks dangerous.
- **A full end-to-end capture-avoidance proof test** (§3).

## How to extend this

New adversarial cases belong in `proofs/soundness/`, following the existing
files' pattern: a comment explaining what property is being tested and why
it matters, then either a `;;; ` marker (required for anything that fails
while *closing* a block — `expect`, per its documented limitation in
`kurt-doc.md` §9.6, cannot observe that) or `expect "KIND"` (for a failure
from an ordinary statement). Update this file alongside any new finding.
