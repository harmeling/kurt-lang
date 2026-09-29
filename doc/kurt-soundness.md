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

## 0. The most severe bug found in this whole audit: `forall-elim` could prove any two things equal

**Found while working on `set.kurt`, but has nothing to do with `set.kurt`
at all.** `load logic, equality` — nothing else, no other theory involved —
let `f = g` be derived for two freshly-declared, completely unrelated
constants, no premise connecting them whatsoever:

    load logic, equality
    const f, g
    f = g          ; used to succeed! ("Proof checked.")

This is about as bad as a soundness bug gets: `logic.kurt` + `equality.kurt`
is very likely the single most common theory combination in the entire
ecosystem (nearly every other theory loads one or both, directly or
transitively), so this wasn't a corner case — any proof anywhere using
`forall`-quantified facts alongside equality reasoning was at risk.

### 0.1 Mechanism

`forall-elim`'s own axiom is `(forall $x %A) implies (sub $x $a %A)`.
Deriving `f = g` via this axiom:

1. **The conclusion decomposes degenerately.** Matching the conclusion
   `sub $x $a %A` against the goal `f = g` uses `generate_all_combinations`'s
   "single-hole decomposition" search, which tries *every* node of the goal
   as a candidate hole — including, for any expression, the trivial "the
   hole is one whole side" decomposition. One such decomposition gives
   `%A := ($x = g)` and `$a := f` (replace the `f` leaf with the hole,
   keep `g`) — perfectly legal on its own; `sub`-based decomposition is
   *supposed* to explore exactly this space, and needs to for legitimate
   proofs.
2. **forall-elim's own premise gets stripped of meaning.** To apply
   forall-elim, its own antecedent — `forall $x %A` — must be satisfied.
   `impl_elim` strips that outer `forall`, since the standard way to
   satisfy "I need a universally-quantified fact" is "show `%A` holds for a
   fresh, arbitrary `$x`" (this is `remove_outer_forall_quantifiers`,
   applied here to forall-elim's *own* defining antecedent). With `%A`
   already bound (from step 1) to `$x = g`, the premise search now just
   needs to establish **`$x = g`** — for the fresh `$x` that's supposed to
   mean "any value whatsoever".
3. **The fresh eigenvariable gets resolved anyway.** Nothing prevented that
   `$x` from being unified straight to the concrete value `g` while
   searching the theory for a match — here, against "equal-intro"'s
   `$a = $a` (which forces `$x` and `g` to be the same thing). A variable
   that's supposed to mean "true no matter what this is" instead got
   treated as an ordinary, freely-assignable unification variable — which
   is exactly what "for all x" must *not* permit. That's the actual bug:
   not the decomposition (needed elsewhere), not the premise-stripping
   (needed elsewhere) — the missing piece was that the **eigenvariable
   introduced specifically to stand for "an arbitrary instance" was never
   protected from being resolved to a specific one** during the search for
   that instance.

The same defect independently broke a genuine proof that had nothing to do
with equality at all: `proofs/mafi1/001-two-equal-sets.kurt` (a real
distributive-law proof, `A∩(B∪C) = (A∩B)∪(A∩C)`) turned out to have been
passing *only* because of this exact bug — several steps silently jumped
straight from `x ∈ (A∩B)` to `x ∈ (A∩B)∪(A∩C)` via the same "eigenvariable
resolved to a lucky concrete value" mechanism, which would just as happily
have "proven" membership in that union from membership in *any* unrelated
set. Fixing the underlying bug correctly rejected that shortcut; the proof
needed (and now has) the actually-missing `or-intro` steps to reach the
same true conclusion soundly. See §0.3.

### 0.2 The fix

`impl_elim`'s premise-handling now tracks which variable(s) were freshly
introduced specifically to stand in for a stripped-off `forall` in the
*premise* it's trying to satisfy, and blocks them (`State.block_as_domain`)
before searching the theory for that premise. Blocking as *domain* only
(not `block_always`, which would also block them as *range*) is
deliberate: it stops the eigenvariable from being *assigned* a concrete
value, while still allowing a genuinely matching fact's *own* variable to
be unified onto it — which is exactly how the legitimate case (matching one
generic/fresh instance against another) keeps working.

Getting this right took two attempts:

- **First attempt (wrong): reuse `remove_outer_forall_quantifiers`
  independently on the premise and the conclusion.** This generated a
  fresh name for the premise's own copy of `$x`, but `%A` is an opaque
  schema token that doesn't literally *contain* `$x` — so the rename was a
  no-op, and the conclusion's separately-extracted, *never-renamed* `$x`
  was the one that actually ended up inside whatever `%A` matched. Blocking
  the (unused) fresh name from the premise-only rename blocked nothing
  real; the bug reproduced unchanged.
- **Second attempt (also wrong, closer): rename the premise's `$x` and
  apply the same substitution to the conclusion via `apply_subst`.**
  `apply_subst` is (correctly, for ordinary substitution) capture-avoiding:
  it refuses to substitute into a bindop's own binder slot. But `sub` is
  itself registered as a bindop, and forall-elim's conclusion is
  `sub $x $a %A` — so `apply_subst` refused to rename `$x` sitting right in
  `sub`'s own binder position, again leaving premise and conclusion
  referring to two different variables for what must be the same one.
- **Working fix: a dedicated helper, `strip_premise_with_synced_conclusion`**,
  that strips the premise's outer foralls and renames *both* the premise
  and the conclusion together using a **pure structural replacement**
  (`replace_token_value`) rather than `apply_subst` — safe here
  specifically because the name being replaced is always a synthetic,
  globally-unique one (from `rename_all_vars`'s own counter), so there's no
  capture risk to avoid in the first place. `impl_elim` then blocks exactly
  the resulting fresh name(s) before the premise search.

One more subtlety: the *conclusion* can independently have its own outer
forall(s) unrelated to the premise's (e.g. `induction`'s premise is
`and`-headed, but its conclusion is `forall $n in Nat (...)`) — those still
need stripping too, just via the plain (fresh-var-discarding)
`remove_outer_forall_quantifiers`, since they get resolved by unifying
against the real goal, not by a premise search, so this specific danger
doesn't apply to them.

### 0.3 Verification

- Confirmed the bug reproduces with the *original*, untouched code (before
  any change this session), with nothing but `load logic, equality` — ruling
  out any chance this was introduced by other work this session.
- After the fix, ran the *entire* proof suite and manually inspected every
  regression: two genuine proofs initially broke
  (`proofs/linear-algebra/injective2.kurt`,
  `proofs/mafi1/001-two-equal-sets.kurt`) — traced both to confirm they were
  passing *only* via this same unsound shortcut, not a false positive in
  the fix. `injective2.kurt` needed no content change (a missing
  independent-conclusion-stripping case in the fix itself, see above);
  `001-two-equal-sets.kurt` needed real, additional `or-intro` steps that
  the original proof had been silently skipping.
- Regression tests: `proofs/soundness/forall-elim-cannot-prove-arbitrary-equality.kurt`
  (the minimal reproduction, now correctly rejected) and
  `proofs/soundness/forall-elim-still-works-legitimately.kurt` (confirms the
  fix doesn't overcorrect into breaking genuine `forall`-instantiation).
- Adversarially retried the same exploit shape against several other theory
  combinations (`arith`+`logic`, `modal`+`logic`, bare `logic`+`equality`
  with different constant names) — all correctly rejected post-fix.

## 0b. A second, narrower instance of the same eigenvariable class of bug: `impl_elim`'s `is_iff` direct-match path

Found while investigating a much narrower-looking report ("a declared-but-
unconstrained `var` can get treated as boolean anyway"), which turned out
to be a *symptom* of a second, independent case of exactly the same
underlying mistake as §0: a variable that's supposed to mean "this
specific, if arbitrary, value" gets unified away to whatever value makes
some unrelated axiom fire, instead of being required to hold as literally
stated.

### 0b.1 Mechanism

Minimal reproduction, `load prop` alone:

    var a
    bool C
    a iff C

This "derives" `a iff C` — for two symbols with *no axiom whatsoever*
connecting them — citing `"not-not"` (`%A iff (not (not %A))`) as the
reason. The same thing happens with `%A iff C` written directly (no `var`
involved at all), confirming the `var`/auto-boolean-inference angle was
just how the bug was first noticed, not the actual cause.

`impl_elim`'s handling of an `iff`-shaped theory fact (`elif is_iff
(formula_expr):`) tries three things: rewrite as `LHS implies RHS` and
recurse, rewrite as `RHS implies LHS` and recurse, and — the "third
attempt" — unify the goal directly against the *whole*, unstripped `iff`
fact (`unify_exprs_with_patterns([(expr, formula_expr)], s, kb)`), meant to
catch a goal that's a direct restatement of the stored fact. The first two
attempts recurse into the plain-implication branch of `impl_elim`, which
*does* protect itself: right before matching a conclusion, it computes
`free_bound_vars(expr, kb)` (on `expr` *after* `derive_expr`'s own
rename-to-a-fresh-internal-name step) and blocks those names as domain —
exactly the "this variable must not be assigned a value, only unified onto
by a candidate's own pattern variable" protection from §0. The third
attempt, though, unifies `expr` directly using the caller's `s` completely
unchanged — it never adds this blocking at all. So `a` (renamed internally
to some fresh `$$NN`/`%%NN` name by `derive_expr`, per whatever `is_bool`
says about it — irrelevant to the bug itself) is a genuinely free variable
at that point, and nothing stops the third attempt from binding it
straight to `not (not C)`, satisfying `not-not`'s shape for *some* value of
`a` that was never asserted to hold, rather than for whatever `a` actually,
specifically is.

Why the caller (`eval_qed`, or `eval_expression` for a bare top-level
statement) can't fix this from the outside by pre-computing a blocked
`State`: `derive_expr` renames the goal to a *fresh* internal name on
*every call* (`rename_all_vars`'s counters are global and monotonic, not
content-addressed), so a caller that blocks the goal's free variables
*before* calling `derive_expr` is blocking a name that no longer appears
anywhere in the expression being matched by the time matching happens —
harmless, but completely inert. This is why the plain-implication branch
recomputes its own blocking internally, from the already-renamed `expr`,
instead of trusting whatever the caller passed in; the `is_iff` third
attempt just never got the same treatment.

### 0b.2 The fix

Added the identical blocking computation immediately before the third
attempt's `unify_exprs_with_patterns` call, unioned with whatever the
caller already had blocked (mirrors the plain-implication branch exactly,
just applied one branch earlier). No changes needed to `eval_qed`,
`eval_expression`, or the `var`/boolean-inference heuristic that first
surfaced this — that heuristic (auto-inferring an unconstrained, not-yet-
used symbol as boolean the first time it appears in a boolean position)
turned out to be intentional, load-bearing behavior relied on by several
existing proofs (e.g. `proofs/natural-deduction/and-sym.kurt`, which
declares `var a, b` and relies on exactly this inference instead of
`%`-prefixed schema variables) — confirmed by trying to tighten it first
(requiring `not kb.is_var(s)`) and watching four legitimate proofs break.
The real bug was never "a `var` symbol shouldn't be inferred boolean" —
it was "whatever a bare statement's own free variable turns out to be, it
must not be unifiable away during that statement's own derivation," which
is a property of `impl_elim`, not of the boolean-inference heuristic.

### 0b.3 Verification

- Confirmed via `git stash` that the minimal reproduction above succeeds
  (wrongly) on the code from before this fix, and is correctly rejected
  after.
- Checked every other `sym`-declared operator in the shipped theories
  (`=`, `≠`, `or`, `+`, `*`) for an axiom of the same exploitable shape
  ("bare variable on one side, that same variable wrapped in something on
  the other") — `not-not` is the only one that currently has it, but the
  fix is general (protects the `is_iff` branch for any `iff`-shaped fact,
  present or future), not a patch against this one axiom.
- Verified legitimate `iff` reasoning is unaffected: `not (not P)` still
  derives from `P` via `not-not`, and a goal with no free variables of its
  own (e.g. `P iff (not (not P))` for a plain boolean constant `P`) still
  matches the third attempt directly, since blocking an empty set of
  variables is a no-op.
- Ran the full test suite (95/95) after the fix, including
  `and-sym.kurt` and every other `var`-as-implicit-schema-variable proof.
- Regression test: `proofs/soundness/iff-third-attempt-blocks-eigenvariable.kurt`.

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

**Update, since fixed: `forall`/`exists` are now hard-coded syntax, not just
`logic.kurt` declarations.** The wrinkle above used to read "`let`'s
forall-wrapping always uses the literal symbol `forall`, regardless of
whether the current theory has declared it a `bindop`" — which turned out
to be much worse than a footgun once actually tested. `theory_append`/
`show_append` (every formula ever stored) and `all_theory()` (every
derivation search) already unconditionally special-case any expression
headed by the literal symbol `forall`, via `remove_outer_forall_quantifiers`
— completely independent of `let`, and independent of whether `forall` is
declared a `bindop` anywhere. Without that declaration, the bare word
`forall` still parses (as an ordinary, flatly space-applied symbol) but
produces the wrong shape, and the very first formula mentioning it crashed
with a raw, uncaught `AssertionError` — reachable with nothing more than
`use forall x A x` and no `load logic`, no `let` involved at all.

**Fixed two ways:** (1) `forall`/`exists`'s syntax (arity, `bindop`, bool
signature, `∀`/`∃` aliases) is now declared directly in `initial_kb`
(`kurt.py`) and documented in `minimal.kurt`, exactly like `and`/`implies`'s
syntax already was — removed from `logic.kurt`, which now only supplies
their *axioms* (`forall-elim`, `exists-intro`). This means `let`/`use
forall ...`/etc. all work correctly with no `load` at all now — and, as a
side effect, forall-elim already happens "for free" via the always-on
auto-stripping (§1), without needing `logic.kurt`'s axiom. (2) Independent
of that, `remove_outer_forall_quantifiers` and `all_theory()`'s analogous
check no longer `assert` the expected shape — they raise a clean
`KurtException` if it's ever wrong, as defense in depth in case this
invariant is broken some other way in the future.

This surfaced one more thing worth recording: `sub` (the other hard-coded
`bindop`) is deliberately *not* registered `const` — only added to
`.used` directly, so it's classified without being either `const` or `var`.
Copying that exact pattern for `forall`/`exists` at first (add to `.used`
without `const`) suppressed `_add_new_symbols`'s normal "first use of an
unclassified symbol becomes `const`" fallback, which is what used to
silently classify `forall` as `const` the moment `logic.kurt`'s own
`forall-elim` axiom mentioned it. Without that, `extract_by_condition` (used
by `def`'s left/right-hand-side scan, which has no bound-variable
awareness at all) started treating the bare word `forall` as an
unclassified "new symbol", breaking any `def ... iff ∀$x (...)` proof —
e.g. `proofs/linear-algebra/injective2.kurt`. Fixed by registering
`forall`/`exists` as `const` explicitly instead, matching `true`/`implies`/
`and`'s pattern rather than `sub`'s.

### 2.2 Bug found and fixed: an explicitly-`forall`-quantified boolean variable lost its boolean classification

Found while investigating the "mixed boolean/non-boolean variables in one
`let`" question below. `remove_outer_forall_quantifiers` strips an outer
`forall` at storage time and replaces its bound variable with a fresh
internal name (`new_var_name()`, `$$NN`) — but it did this unconditionally,
even when the bound variable was a `%`-prefixed *boolean* schema variable,
which needs a fresh *boolean* name instead (`new_bool_var_name()`, `%%NN`) to
stay recognized as boolean afterwards. `rename_all_vars_rec`'s own
bindop-handling branch, a few lines below in the same file, already gets
this right (`if kb.is_bool(var): new_var = new_bool_var_name() ...`) — the
two code paths had simply drifted apart.

This is not just a cosmetic mismatch: `impl_elim`'s case for a bare
boolean-variable premise (matching a *whole* conclusion unconditionally, see
§6 below) is gated on `is_bool_var_token`, which checks exactly this
classification. So an axiom written with an explicit `forall %A (...)` — a
natural, idiomatic way to quantify over a whole proposition — silently
stopped being usable via that mechanism the moment it was stored, a false
rejection. Confirmed by direct inspection of the stored `simplified_expr`
(`forall %A (%A implies P)` stored `%A` as a non-boolean `$$NN` before the
fix, a boolean `%%NN` after) and by a real derivation that only succeeded
after the fix: `proofs/soundness/forall-quantified-boolean-var-classification.kurt`.
Fixed by making `remove_outer_forall_quantifiers` check `kb.is_bool(bound_var)`
the same way `rename_all_vars_rec` already does.

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

**Now also confirmed end-to-end, not just at the unit level.**
`proofs/soundness/capture-avoidance-blocks-unsound-instantiation.kurt`
tries the classic textbook counterexample through a real derivation: from
`forall x (exists y (not (x = y)))`, naively substituting the outer `x`
with the *same name* as the inner bound `y` would "derive" `exists y (not
(y = y))` — something different from itself, never true. Confirmed
rejected. Its companion, `capture-avoidance-safe-instantiation.kurt`,
checks the *same* premise still lets a genuinely safe instantiation
through (substituting `x` with a fresh, unrelated constant) — confirming
the first file's rejection is really about capture, not some unrelated
limitation silently blocking that whole shape of derivation.

### 3.1 Bug found and fixed: `def`'s new-symbol scan was blind to bound variables

The `def-with-forall-in-rhs.kurt` note in §2.1 mentioned that `extract_by_condition`
(used by `def`'s "exactly one new constant on the LHS, zero new symbols on the
RHS" check) has no bound-variable awareness at all, and only "works" because
idiomatic Kurt always uses `$`-prefixed variables in bound positions (`$x`,
`$y`, ...), which are unconditionally classified as variables by prefix alone
regardless of scope. Investigated properly this time (task from `todo-claude.md`,
the mirror-image of the already-fixed RHS-forall/exists issue): a plain,
non-prefixed bound variable is affected on **both** sides, in two different
directions.

- **RHS false rejection**: `def p iff forall x Q x` (bound `x`, no `$`) was
  wrongly rejected — `x` was reported as a disallowed "new symbol" on the RHS,
  even though it's just as validly scoped as `$x` would be. Merely an
  annoyance (over-restrictive, not unsound) but a real ergonomic gap; fixed.
- **LHS misdiagnosis** (the more concerning direction, since it's a false
  *accept*, not a false reject): `def (forall x true) iff true` was silently
  accepted, with `x` — a bound variable, scoped only to that `forall` — logged
  as "defining `x`", i.e. `def`'s own validation believed it was introducing a
  new global constant named `x`. Checked whether this actually leaks anything:
  it doesn't — `kb.is_const('x')` and `kb.is_var('x')` are both `False`
  afterwards, because `theory_append`'s real storage pipeline
  (`remove_outer_forall_quantifiers` + `rename_all_vars`) scopes `x` correctly
  regardless of what `eval_def`'s separate check believed, and nothing reads
  `eval_def`'s returned "new constant" name except the log line. So this was a
  misleading diagnostic, not an exploitable soundness hole — but still worth
  fixing, since a check whose entire job is "identify the one new symbol"
  should not be fooled by a symbol that isn't new at all.

Both fixed together by making `extract_by_condition` bound-variable-aware,
mirroring the existing `contains` helper (§2 above): it now takes `kb` and
tracks `bound_vars` through any `is_bindop`-headed subexpression, excluding
them from candidacy exactly like `contains` already excludes them from its
symbol search. Regression tests:
`proofs/soundness/def-bound-var-not-new-symbol.kurt` (RHS false-rejection
fixed) and `proofs/soundness/def-lhs-bound-var-rejected.kurt` (LHS
misdiagnosis: now correctly rejected instead of silently mislabeled).

### 3.2 Checked: fresh internal names can't collide with a user-typed variable

`new_var_name()`/`new_bool_var_name()` — used by `rename_all_vars_rec` (§2.2,
§3 above) and `remove_outer_forall_quantifiers` to generate the fresh names
that back every renamed free/bound variable — hand out names like `$$07`/
`%%07`, reasoning (per the comment at their definition) that "the `$$`
ensures that it is not a kurt variable that the user can define". This
invariant matters: if a user could ever type a variable whose name
coincided with a live counter value, it would silently alias an internal
substitution variable, which is exactly the kind of thing capture-avoidance
(§3) is supposed to prevent.

This was flagged in `todo-claude.md` as *unverified* — and, on first pass,
wrongly claimed to be a real gap ("a user *can* type a variable named
literally `$$foo`"). Checked properly this time: the lexer's `SYMBOL`
pattern (the `scanner` regex in `kurt.py`) is `[$%@]?[A-Za-z][A-Za-z0-9]*` —
at most **one** leading `$`/`%`/`@`, immediately followed by a letter. A
doubled prefix like `$$foo`/`%%foo` cannot match that (or any other
branch); it falls through to the lexer's catch-all `ERROR` group and raises
a `SyntaxError` before parsing even begins — confirmed directly (`var
$$foo` → `SyntaxError: scanning error while scanning \`$\``). So no source
text a user writes can ever lex into a token that collides with a generated
name: the invariant holds **by construction** (grammar-level), not merely
by convention as the original comment implied. No code change was needed.
Locked in by `proofs/soundness/dollar-dollar-prefix-unparseable.kurt`.

### 3.3 Bug found and fixed: `equal_expr` was blind to alpha-equivalence

Resolves `todo.md`'s open question, "check whether we need a version of
`equal_expr` that allows bounded renaming" — yes, confirmed with a real
failing proof, not just a theoretical worry.

`equal_expr` (used by `pick`'s existential-match check, the no-op-restatement
shortcut, the `sub`-decomposition search, and the core unifier's fast-path)
used to be pure token-by-token structural equality, with no notion of
alpha-equivalence at all. This broke `pick`/exists-elim outright whenever the
existential's body contained *another* quantifier: `rename_all_vars` renames
*every* bound variable (not just the outermost) to a fresh internal name at
storage time, so `exists x (forall y (R x y))`'s stored `simplified_expr`
becomes `exists $$05 (forall $$06 (R $$05 $$06))`. `eval_pick` substitutes
the witness for `$$05` and compares the result against the user's own
literally-typed fact — `forall $$06 (R c $$06)` was never going to
structurally match the user's `forall y (R c y))`, even though they're the
same formula. Confirmed directly: `pick c with forall y (R c y)` (given
`exists x (forall y (R x y))`) raised `ProofError: can not find an
existential formula that matches the \`pick\`` before the fix.

Fixed by making `equal_expr` genuinely alpha-equivalence-aware: it now takes
`kb` and threads a pair of bound-variable correspondence maps through the
comparison (`equal_expr_alpha`), extending the map whenever both sides are
headed by the same `is_bindop` symbol. Only bound-variable *name* tokens get
this leniency — constants, schema variables (`%A`/`$x` used as free
placeholders, not as a binder's own name), and operators still require exact
literal identity, so this can never make two genuinely different formulas
compare equal (verified: different predicates, different quantifier kinds, a
free variable vs. a same-named bound one, and shadowing all still behave
correctly — see `tests/test_equal_expr_alpha.py`). All 5 call sites updated
to pass `kb`. Regression: `proofs/soundness/pick-with-nested-quantifier.kurt`
(now succeeds) and its companion `pick-nested-quantifier-still-rejects-wrong-fact.kurt`
(a genuinely wrong fact is still rejected).

### 3.4 Bug found and fixed: `pick` crashed (not just failed) inside `expect`

Found while writing the regression test above — unrelated to the
`equal_expr` fix itself, but uncovered by it. Wrapping a *failing* `pick` in
`expect "ProofError"` crashed the whole interpreter with an uncaught
`AssertionError: BUG: we should be one level up`, instead of `expect`
either catching it cleanly or failing normally (its documented behavior for
cases it can't observe, `kurt-doc.md` §9.6).

Root cause: unlike `let`/`assume`/`case`, which push their level in
`eval_keyword_expression` *before* calling anything that could raise,
`pick`'s level is pushed *inside* `eval_pick` itself, only after checking a
matching existential exists — so `eval_pick` can raise (the ordinary "no
matching existential" `ProofError`) before ever opening a level.
`eval_keyword_expression`'s `'pick'` branch caught any failure and
unconditionally called `kb.pop_level()` to clean up — correct if `eval_pick`
failed *after* opening its level, wrong if it never opened one: that pop
instead discarded the *caller's* own already-open level (`expect`'s, in this
case), corrupting the level stack and crashing on the next `pop_level` call.
Fixed by only popping when `eval_pick` actually pushed a level (comparing
`kb.level` before/after the call). Regression:
`proofs/soundness/expect-pick-no-crash.kurt`.

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

### 4.1 Bug found and fixed: `arity`/`bindop` didn't check the ancestor chain

Found while investigating `todo-claude.md`'s "file-local variables /
explicit theory export" gap — specifically, checking whether loading two
unrelated theories that happen to redeclare the same symbol name could
cause anything worse than an ugly namespace clash. It could: not an
accepted-false-proof (I didn't find a way to turn this into one — old
formulas remain self-consistent data regardless of a symbol's arity
changing later), but a genuine, silent data-loss inconsistency.

Every `add_*` "already declared" guard is supposed to check the *whole*
ancestor chain, the same way the corresponding `is_infix`/`is_const`/
`bool_sig`/etc. lookups already do (confirmed by reading all of them:
`add_prefix`, `add_infix`, `add_postfix`, `add_var`, `add_const`,
`add_alias`, `add_bool`, `add_flat`, `add_sym`, `add_chain` all correctly go
through an ancestor-aware helper). `add_arity` and `add_bindop` didn't —
they checked `fun in self.arity` / `self.arity[fun]` directly, which only
sees the *current* level's own dict. This bit in exactly the case ancestor
chains exist for: `load` opens a fresh child ("sandbox") level per file,
whose own `arity` dict starts empty. Loading two *separate* files that each
declare a *different* arity for the same symbol name — `arity P 1` in one,
`arity P 2` in the other — silently succeeded, with the second value
silently overwriting the first the moment its level merged back in (no
error at all, confirmed directly: `kb.arity` ended up `{'P': 2}`, with no
trace `P` was ever `1`). The *same* redeclaration within one file correctly
raises `EvalError: arity of symbol \`P\` has been already set to 1` — so
behavior depended entirely on how a theory author happened to split
declarations across files, an inconsistency in its own right regardless of
the silent-overwrite risk.

The reverse direction also turned up a genuine false rejection: `add_bindop`
declaring a symbol as a binding operator *inside a nested block*
(`sandbox`/`assume`/`let`/...) whose arity was declared on an *ancestor*
level wrongly raised "before declaring symbol as variable binding, you must
set its arity", even though the arity genuinely was set — just not in the
current level's own dict.

Fixed by adding a proper ancestor-aware `is_arity_set` (mirroring
`is_infix`/`is_const`/etc.) and using it (plus the already-ancestor-aware
`get_arity`) in both `add_arity` and `add_bindop` instead of raw dict
access. Regression tests:
`proofs/soundness/arity-redeclaration-across-load-rejected.kurt` (the
silent-overwrite direction, now correctly rejected) and
`bindop-sees-ancestor-arity.kurt` (the false-rejection direction, now
correctly accepted).

## 5. Guard against silently losing these checks

Several of the checks above (and plenty of internal invariants elsewhere:
occurs-checks, level-stack bookkeeping, ...) are plain Python `assert`s
(`BUG:` messages) rather than `raise KurtException` — appropriate, since
they're "can't happen" invariants, not user-facing errors. But `python
-O`/`-OO` strips all `assert`s at compile time, which would silently
disable them. `main()` now refuses to run at all under `-O`/`-OO`
(`if not __debug__: ... sys.exit(1)`), so this can't happen unnoticed.

## 6. Open questions, not resolved here

- **Mixed boolean/non-boolean variables in one `let` list** (`let x, %A`) —
  **now investigated and resolved**, though not the way `todo.md`'s framing
  ("check that the quantification either applies to boolean or non-boolean
  vars, but not both") expected. `eval_done`'s forall-wrapping loop does skip
  wrapping conditions where `is_bool_var_token` is true, but this turns out
  to make **no difference to soundness either way**: a bare, top-level `use
  %A implies P` (no `let` at all) already lets `P` be derived completely
  unconditionally, since `%A` freely unifies with anything — even the most
  extreme case, a bare `use %A` with no implication at all, immediately
  makes *any* boolean proposition derivable. This is an inherent property of
  `%`-prefixed schema variables in `use` statements generally (by the same
  logic that makes `use $A implies $A "restatement"` a valid schema: a
  `%`/`$`-prefixed symbol in a `use` axiom means "for any value of this
  symbol", so `use %A` literally asserts "every proposition is true" — a
  false premise from which anything classically follows). `let`'s specific
  skip-wrapping behavior for boolean variables was confirmed, by direct
  comparison, not to add or remove any exploitability beyond what a bare
  `use %A implies ...` already has on its own — `let %A`'s role in any such
  exploit is incidental, not causal. See §2.2 above for a real, unrelated
  bug this investigation *did* turn up (an explicitly `forall`-quantified
  boolean variable losing its boolean classification when stored) — now
  fixed. What remained was a **design/documentation question**, not a
  soundness bug: should Kurt warn a theory author who writes a `use`/`def`
  axiom that's just a bare (or nearly bare) `%`/`$`-prefixed variable, since
  it's easy to write one by accident without realizing how strong a claim it
  makes? Resolved as a **warning, not an error** — `bare_bool_schema_axiom_warning`
  (called from `eval_use`, so it covers `def` too, since `eval_def` delegates
  to it) prints a `Warning:` to stderr for the obvious shapes: a bare `use
  %A`; `use %A implies X` (or `def d iff %A`) where the bare variable doesn't
  reappear on the other side. It deliberately does not reject — an axiom
  shaped like this is occasionally written on purpose (much like `use false`
  is allowed outright) — and it deliberately only pattern-matches these
  specific shapes rather than trying to decide in general whether an
  arbitrary formula is a tautology (undecidable/intractable for arbitrary
  user-declared connectives). Confirmed against all of `prop.kurt`/`logic.kurt`'s
  real axioms that none of them false-positive (e.g. `%A implies %A or %B`
  "or-intro" doesn't warn, since `%A` reappears in the conclusion — the
  premise still has to be matched against something you actually derived,
  unlike the trap shapes above). See `tests/test_bare_bool_schema_warning.py`
  for the unit-level cases and `doc/kurt-doc.md` §6.2 for the user-facing
  description.

  **Caveat: `iff`/`=` are recognized by literal symbol name, not by
  semantics.** `bare_bool_schema_axiom_warning` checks `op == IMPL_SYMBOL`/
  `op in (EQUAL_SYMBOL, IFF_SYMBOL)` — plain Python string comparison against
  the hardcoded names `'implies'`/`'='`/`'iff'`. This is not new: `eval_def`'s
  own dispatch (§3.1) already recognizes `def`'s `=`/`iff` the same
  name-based way, and `iff` itself is not hardcoded at all — it's declared
  via `infix iff ...` in `prop.kurt`, like any user symbol. So if a theory
  ever repurposed the *name* `iff` for an operator unrelated to logical
  equivalence, this warning would still fire (or stay silent) based on that
  name match alone. Not a soundness problem — the warning never blocks
  anything, so the worst case is a spurious or missing hint — but worth
  knowing if a warning ever looks wrong: check what `iff` actually means in
  that theory first.

  **Considered and rejected for now: a user-extensible `avoid PATTERN, ...`
  keyword**, so a theory author could register additional warning shapes
  instead of only the ones hardcoded above. The blocker isn't syntax, it's
  semantics: the actual danger condition — "does this schema variable fail
  to reappear elsewhere in the formula" — is a negative-occurrence check,
  not an ordinary structural pattern match. A naive `avoid %A implies %B`
  declaration matched via Kurt's existing unification would also flag
  legitimate axioms like `%A implies %A or %B` ("or-intro"), since plain
  pattern-matching can't express "as long as %A doesn't occur here". Even a
  wildcard-based notation (`avoid %A iff _, _ iff %A`, with `_` meaning "any
  expression") doesn't sidestep this: for it to be correct, `_` would have to
  mean "any expression *not containing* the other named variable in this
  pattern" rather than the ordinary Prolog-style "matches literally
  anything" — which is exactly the same negative-occurrence primitive again,
  just spelled with underscore syntax. Building this properly would mean
  exposing something like `contains`/`State.occurs` (currently internal
  Python helpers, §2 and §3) as a genuine Kurt-level primitive with new
  matcher semantics, not reusing the existing pattern-matcher as-is — a
  real, if self-contained, language feature, not a quick extension of the
  current warning. Filed as an idea, not implemented.
- **`case` exhaustiveness** — nothing checks that a sequence of `case`
  blocks actually covers a real disjunction before the implicit `or-elim`
  step; a missing case just means the final combining claim fails to
  derive (a completeness gap, not a soundness one, since or-elim itself
  still requires the real `%A or %B` axiom to be in scope) — mentioned for
  completeness, not because it looks dangerous.
- ~~**`equal-elim`-driven substitution can't replace a multi-argument chunk of
  a `flat` operator's argument list**~~ — **fixed, see §8.2.** Original diagnosis:
  Found while writing a real test proof for `arith.kurt`'s factorial
  recursion (`proofs/arithmetic/factorial-recursion.kurt`): chaining a
  *second* application of "factorial-step" (to go on from `1! = 1` to prove
  `2! = 2`) reliably failed to substitute `1! = 1 * 1` into `2 * 1!`.
  Traced it precisely (adding temporary instrumentation to `impl_elim` and
  inspecting every candidate decomposition tried): the target
  `2! = 1 * 1 * 2` is stored as a genuinely flat, 3-argument node
  `[*, 1, 1, 2]` — `flatten_all` throws away the grouping that would say
  "the first two of these three came from one sub-expression, `1 * 1`".
  `all_single_hole_decompositions` (which `equal-elim`'s matching relies on
  to find a substitution site) only ever replaces *one syntactic node* per
  decomposition — there is no addressable node in `[*, 1, 1, 2]` that
  corresponds to "elements 0 and 1 together", so no decomposition can ever
  represent "substitute `1 * 1` back in for `1!`" once the expression has
  already been flattened. Confirmed this only bites when the *substituted
  value* is itself a multi-argument expression under the *same* flat
  operator as its context (a single-argument/bare-literal RHS, like
  `factorial-base`'s `0! = 1`, works fine at any depth).
  This is exactly `todo.md`'s own "allow multiple replacement in one step
  (is that possible?)" item, previously listed as blocked on "needs a
  concrete motivating example before it's clear whether it's worth the
  complexity" (see `todo-claude.md`) — this factorial-chaining proof *is*
  that concrete example now. Still a completeness gap, not a soundness
  one (it can only make a true goal harder to reach in one step, never a
  false one derivable), and still not fixed here: a real fix means
  `all_single_hole_decompositions` (or a sibling) trying every *subset* of
  a flat node's arguments as a candidate hole, not just every single node —
  a genuine, non-trivial feature (combinatorial cost per flat node, same
  family of concern as the O(n^k) performance items in `todo-claude.md`),
  not a bug fix, so deliberately left as a documented, well-understood gap
  with a real motivating test case rather than attempted under this pass.
- **`set-comprehension` (and any other axiom matched via `sub`-decomposition)
  couldn't match a substitution body with zero occurrences of the bound
  variable — found and fixed.** Minimal repro: `load set` / `const x` /
  `x ∈ { $a | false } ≡ false` failed to derive even though it's true by
  definition — substituting anything for `$a` into a body (`false`) that
  never mentions `$a` in the first place obviously still gives `false`.
  Root cause, traced directly in `generate_all_combinations`: the
  decomposition mechanism (`all_single_hole_decompositions`) only ever
  proposes a candidate `%A` by picking one *existing* node of the concrete
  expression and replacing it with the substitution marker `$x` — every
  candidate it can produce therefore has *exactly one* occurrence of `$x`.
  It structurally cannot propose "zero occurrences, `%A` equals the
  expression verbatim, `$a` is unconstrained" — that shape was simply never
  tried, in the same family as (but distinct from) the flat-operator gap
  above: both are cases where a real, sound decomposition exists but the
  enumeration strategy can't reach it. Fixed by adding exactly that
  candidate: after the per-node loop, also yield `(expr_a, expr)` unchanged
  (still checked against `bound_var_safe`, for consistency, though it's
  vacuously safe here since nothing is actually substituted in this
  branch) — whatever the caller had already pinned `$a` to (or `None`, if
  nothing had) is carried through, since the equation holds for *any* value
  of `$a` once `%A` doesn't mention `$x` at all. Confirmed via `git stash`
  that the minimal repro fails before the fix and succeeds after, and that
  the two known, *separate* lambda-calculus gaps (identity function,
  currying — `proofs/lambda-calculus/known-gaps.kurt`, since removed together with `lambda-calculus.kurt`) are unaffected: those
  fail for a different reason (an alpha-renamed bound variable occupying
  `%A`'s assigned value isn't recognized as *the* substitution site, since
  its name doesn't match the sub-marker's own freshly-renamed name — a
  bound-variable-identity problem, not a missing decomposition candidate).
  This also restores behavior an old, still-present test file
  (`tests/test_gen_all_combinations.py`'s `old_examples`) already expected
  before an earlier "allow only one subterm to be replaced, much more
  efficient" simplification silently dropped it; the *other* difference
  between `old_examples` and today's behavior (multi-occurrence
  decompositions, replacing more than one identical node at once) was a
  deliberate performance simplification, not a bug, and is not restored.
  Regression coverage: `tests/test_gen_all_combinations.py` and
  `tests/test_generate_all_combinations.py` (unit-level, exact candidate
  sets) and `proofs/set-theory/power-set-membership.kurt`'s new
  empty-set-case lines (proof-level, the original motivating example).

## 7. Selective export (`load`'s `local` labels)

Resolves the design question raised alongside "file-local variables /
explicit theory export" in `todo-claude.md`: what exactly should a `load`ed
file make visible? Implemented as: a `use`/`def` axiom or a proved
(`show`/`proof`/`qed`) theorem is exported exactly when it carries a label
that isn't marked `local` (`EXPR local "label"`, a new low-binding-power
continuation registered directly on `initial_kb` — see `local_led`); an
unlabelled fact defaults to *not* exported, same as an explicitly `local`
one. A symbol has no export marking of its own — it's exported exactly
when some exported fact's free symbols (`free_symbols`, mirroring
`contains`'s bound-variable-aware traversal) actually mention it. See
`doc/kurt-doc.md`'s `load` section for the user-facing description.

**Soundness-relevant guarantee, not just an encapsulation nicety:** a
`def`'s two halves (the symbol, and the fact defining what it means) can
never be silently split by export filtering. If a `local`-marked `def`'s
symbol is still needed by some other, exported fact in the same file,
`merge_and_pop` raises a clear `EvalError` naming the symbol rather than
either (a) silently promoting the `local` marking away (which would leak
something the author explicitly asked to keep private) or (b) silently
letting the symbol travel with no definition attached (which would leave
it meaningless — an opaque symbol with a stated arity/type but no axiom
relating it to anything — downstream, with no warning that anything is
missing).

**Two bugs found and fixed while implementing this, both about what
"a fact's free symbols" has to include beyond the obvious:**

1. **Aliases never occur in a formula.** `alias ¬ not` means axioms are
   written with the canonical name (`not`), so `¬` itself is never a "free
   symbol" of any fact — the first version of the closure computation
   missed this, so `¬` silently lost its alias status on export even
   though `not` (its target) survived. Confirmed by a real failure:
   `proofs/natural-deduction/neg-forall.kurt` (`load logic` → `prop`,
   writes `¬P(x)`) misparsed as soon as this closure ran. Fixed by
   iterating alias membership to a fixed point: any alias whose target is
   already exported gets pulled in too.
2. **Custom brackets parse into a synthetic combined token**
   (`{lbracket}$$${rbracket}`, e.g. `{$$$}`), but the pair's own
   `const`/`nud`/`lbp` entries are keyed by the *raw* bracket characters —
   so checking only "does the synthetic name occur in an exported fact"
   correctly finds that the pair is needed, but doesn't by itself preserve
   the raw-character-keyed entries that actually make it parse. Fixed by
   pulling the raw `lbracket`/`rbracket` characters into the exported-symbol
   set whenever their synthetic combined name is found. Exercised for real
   by `set.kurt`'s `{ ... | ... }`/`[ ... ]` (loaded by
   `proofs/mafi1/001-two-equal-sets.kurt`), and directly regression-tested
   for the alias case in
   `proofs/soundness/load-export-alias-of-exported-symbol-survives.kurt`.

**Retrofitting note:** every shipped theory needed auditing for this
change, since an unlabelled `use`/`def` (previously always exported)
silently stops being exported. `prop.kurt`/`logic.kurt`/`equality.kurt`
were already fully labelled. `arith.kurt` (previously all ~50 rules
unlabelled), `set.kurt` (one unlabelled rule), and `modal.kurt` (5 of 6
unlabelled) were retrofitted with labels. `natural.kurt` turned out to
have been silently broken independently of this feature — see the next
paragraph — and was rewritten while fixing it. Confirmed via an explicit
audit (grep every `use`/`def` across `src/kurt/theories/`, cross-check
against every `load` site in `proofs/`/`tutorial/`) that no currently
passing test relied on anything that stopped being exported.

**A genuinely separate, pre-existing bug found along the way, unrelated to
this feature:** `natural.kurt`'s `def Nat = {0, 1, 2, ...}` never actually
worked. Three independent problems stacked up: (1) the lexer greedily
merged adjacent "standard operator" punctuation, so `...}` (no space)
lexed as one token, `'...}'`, swallowing the closing brace — the resulting
unclosed bracket left the parser permanently waiting for more input, which
silently swallowed the *entire rest of the file* with no error at all,
because `read_eval_loop` just breaks out of its loop on EOF while still
"waiting for a continuation"; (2) even with correct tokenization, `,` and
`...` aren't classified as constants anywhere, so `def`'s right-hand-side
check (`extract_by_condition`) rejected them as disallowed "new symbols";
(3) `natural.kurt` never `load`ed `set.kurt` (needed for `in`/`∈`, which
the file's own commented-out "alternative" definition already used) and
declared its own `+` with a binding power (10) weaker than `in`'s (25),
so `$n+1 in Nat` would have parsed as `$n + (1 in Nat)` even if everything
else had worked. None of this was ever caught because `natural.kurt` isn't
`load`ed by anything in `proofs/`/`tutorial/` — nothing ever exercised it.
Rewritten to declare `Nat` as a plain `const`, `load set`, and use a
correctly-binding `+`; regression coverage in `proofs/soundness/`
(`load-export-*.kurt`) and confirmed by direct standalone loading.

**Update: the lexer bug (1) is now fixed at the root, not just documented.**
Bracket characters (`{`/`}`/`[`/`]`) shared a single greedy multi-character
regex alternative with all the other "standard operator" punctuation
(`.`, `:`, `=`, `+`, ...); pulled them out into their own always-single-char
alternative instead, exactly matching how `(`/`)` were already handled
(`scanner`'s "symbols 2" vs. "symbols 4" — see the comment there). Confirmed
`{0, 1, 2, ...}` now lexes correctly with no workaround space, and that
genuinely multi-char operators untouched by this change (`<=`, `>=`, `!=`,
...) still merge as before. This closes the "known gap" that used to be in
`doc/kurt-doc.md` §11 and the matching `todo-claude.md` item. Regression:
`proofs/soundness/bracket-adjacency-lexes-correctly.kurt`.

### 7.1 Bug found and fixed: a labelled bare/conjunction claim silently lost its label

Found while checking whether labelling was really uniform across every
statement kind, not just `use`/`show`/`def` (it's supposed to be — every
statement, keyworded or not, shares `check_expr_label`/`post_process`).
A bare claim (`Q "my-label"`, no `use`/`show`) does correctly carry its
label into the stored `Formula` — confirmed end-to-end, it exports
correctly. But a *conjunction* claim (`P and R "my-label"`, split into
per-conjunct derivation steps and recombined via "and-intro") did not: the
per-conjunct loop in `eval_expression` reused the same Python variable
name, `label`, for each intermediate sub-formula, setting it to `''` for
every conjunct — since this loop runs *before* the combined formula is
built from that same variable, the combined formula always ended up with
an empty label, silently discarding whatever the user wrote, regardless of
whether `local` was involved at all. Fixed by using a separate, clearly
book-ended empty string for the per-conjunct sub-formulas instead of
reassigning `label` itself. Also fixed a related but purely cosmetic gap
found in the same code path: a labelled bare claim's label never showed up
in the log line the way `use`/`show`'s do (embedded in the `reason`
string) — now consistent. Regression:
`proofs/soundness/load-export-bare-claim-label-survives.kurt` and
`load-export-conjunction-label-survives.kurt`.

### 7.2 Bug found and fixed: EOF mid-statement silently truncated the file

A much more severe, general version of the bracket-lexing bug above,
independent of the specific lexer cause: `read_eval_loop`'s file-reading
branch did `if not new_line: break` on EOF, with no check for whether a
statement was still incomplete (`continued == True` — waiting for more
input after a `StopIteration`, e.g. from a genuinely unclosed bracket,
nothing to do with the lexer bug's `...}` case specifically). Hitting EOF
in that state silently discarded the incomplete statement and returned
success — `Proof checked`, exit code 0, for a file whose real last
statement (and anything after the point where it went wrong) was never
actually read. This is precisely the failure mode the whole soundness
audit is about: Kurt reporting a proof fine when it wasn't actually all
checked. Fixed by raising a clear `ParseError` naming the approximate line
instead of breaking, whenever EOF is hit while still `continued`.
Regression: `proofs/soundness/eof-mid-statement-rejected.kurt`.

### 7.3 Bug found and fixed: syntax-only symbols silently dropped by the retrofit itself

Found by a fresh-eyes review pass over the docs, spot-checking `calc`'s
documented operator coverage against reality: `2 ^ 3` (after `load arith`)
parsed as bare space-application, `[2, ^, 3]`, not an infix expression —
`^`'s own `infix ^ 75 75` declaration had silently stopped surviving
`load arith`. Root cause: every axiom in `arith.kurt` that ever mentioned
`^` ("laws of exponents") was already commented out before selective
export existed, so once export was implemented, nothing exported ever
needed `^` — its syntax fell out of the closure entirely. This is exactly
the same shape of gap `!` (factorial) had, already fixed at the time with
a `0! = 1`-style axiom — but `^` was missed during that same retrofit
pass, because "does every *retrofitted* theory still parse the same way"
was never actually checked file-by-file, only "does the existing test
suite still pass" (§7's own retrofit note). A second, independent instance
of the same gap turned up in the same pass: `prop.kurt`'s `invimplies`
(backwards implication, alias `⇐`) had full syntax (`infix`, `bool`,
`chain`, `alias`) but — unlike every other operator in that file — no
defining axiom relating it to `implies` at all; a pre-existing gap that
simply didn't matter before selective export (everything was
unconditionally exported regardless of axioms) but became a real,
observable break once it did.

Fixed both the same way: added a genuine, unconditionally-true axiom that
actually mentions the symbol (`$a ^ 1 = $a` for `^`, chosen over
`$a ^ 0 = 1` specifically to dodge the 0^0-undefined edge case; the
natural `(%A invimplies %B) iff (%B implies %A)` for `invimplies`).
Regression: `proofs/soundness/load-arith-power-syntax-survives.kurt` and
`load-prop-invimplies-syntax-and-def-survive.kurt`.

**Also added a general safeguard**, since "check whether every retrofitted
theory's syntax still works" is exactly the kind of thing that's easy to
forget to re-check by hand after some future edit:
`tests/test_theory_syntax_survives_load.py` declares every `infix`/
`prefix`/`postfix` symbol found in each shipped theory's own source text
and asserts each one survives that file's own `load` — confirmed this
would have caught both bugs above (reverting the two fixes reproduces
both failures). One symbol pair is deliberately exempted: `set.kurt`'s
`:`/`→` (mapping notation) genuinely has no axioms written yet at all
(the file's own comment admits "two mappings are equal if they give the
same output for all inputs" was never implemented) — that's a real,
separate incompleteness, not the same kind of oversight, so it's excluded
from the check rather than papered over with an invented axiom.

### 7.4 Bug found and fixed: a failed conditioned-quantifier goal crashed instead of raising `ProofError`

Found while assessing `natural.kurt`'s induction axiom for the first
time — it turned out nothing anywhere in the repo had ever loaded
`natural.kurt` outside its own self-check (0 files, confirmed by grep), so
its one real axiom had never actually been exercised end-to-end. Writing
a first real test of it (`P 0`, a step fact, then claiming `forall $n in
Nat P $n`) surfaced not a soundness problem with the axiom itself, but an
unrelated, general robustness bug with nothing specific to `natural.kurt`
or induction: **any** failed derivation of a *conditioned* quantifier goal
(`forall $x in Nat ...`, `forall $x>0 ...`, and the `exists` equivalents)
crashed with an internal `AssertionError` instead of a clean `ProofError`
— confirmed independently with `set.kurt`'s `in`, no `natural.kurt`
involved at all.

Root cause: `remove_outer_forall_quantifiers` desugars `forall $x (cond)
body` into `forall $x (cond implies body)` by synthesizing a plain
`Token(label='SYMBOL', value='implies')` with no `column` (defaults to
`None`). Harmless when derivation *succeeds* — the synthetic token is
purely internal and never shown to the user — but when derivation
*fails*, `get_column` (used to build the `ProofError`'s message) asserts
every token it walks down to has a real integer column, and hits this one
instead. Fixed by giving the synthetic `implies` token a column borrowed
from the condition it wraps (which does have one, since it came from real
source text). Regression:
`proofs/soundness/conditioned-quantifier-failure-does-not-crash.kurt`.
(Since §8.11, a condition isn't turned into an implication by the engine at
all, so the synthetic token is gone; the regression test stays.)

Once the crash was out of the way, `natural.kurt`'s induction axiom
itself checked out as functionally correct — `(P 0) and (forall $n in Nat
(P $n implies P ($n+1)))` derives `forall $n in Nat P $n` via one
`impl_elim` step, as expected. The ergonomic catch (not a bug): the base
case and step must be phrased as a single conjunction, not two separate
`use` facts, since `impl_elim` only does one hop and needs the whole
antecedent to match at once — the same single-hop limitation already
noted in §6.1, not something specific to this axiom.

### 7.5 Bug found and fixed: `modal.kurt`'s axioms only worked for two hardcoded propositions

Found while writing `modal.kurt`'s first-ever real test proofs (as
opposed to its one existing "usage," a pure load-mechanics smoke test
that never actually proved anything modal). Every axiom in the file
(`diamond-def`, `box-def`, `diamond-distrib-or`, `box-distrib-and`, `K`,
`T`) was written with plain symbols (`p`, `q`, `A`, `B`) instead of
`%`-prefixed schema variables, unlike every other axiom in every other
shipped theory. A `use` axiom's non-`%`-prefixed symbols aren't
wildcards — they're the literal declared constants — so every one of
these axioms only ever applied to the two specific propositions the file
itself happened to declare. Confirmed directly: with the un-prefixed
version, `use □(X ⇒ Y)` and `use □X` could never derive `□Y` for a
newly-declared `X`/`Y`; only the literal `□(p ⇒ q)` and `□p` could ever
derive `□q`. This is not a soundness bug — a false statement never
became provable — but it made the whole file close to useless for actual
reasoning: you could only ever apply `K` (or anything else in the file)
to two hardcoded atoms, never to a proposition you actually cared about.

Fixed by rewriting all six axioms with `%p`/`%q` (matching `prop.kurt`'s
`%A`/`%B` convention), and removing the now-unneeded `bool A, B, p, q`
declaration — only `b`/`d` (the box/diamond operator symbols) are real
constants now. Regression: `proofs/modal-logic/*.kurt`, deliberately
using `X`/`Y` rather than the file's own `p`/`q` example symbols so they
would have caught this; confirmed by reverting the fix and re-running —
all three fail.

## 8. Matcher changes for the `proofs-not-yet` backlog (2026-09-25)

Made while moving `gauss.kurt`, `solve-math-equation.kurt`, `chains.kurt`, … from
`proofs-not-yet/` into the test suite. All but §8.1 widen what the matcher *can find*; the
argument for each is why nothing false becomes findable.

### 8.1 Bug found and fixed: a `forall` inside a conjunctive premise never matched

Stored facts have their outer `forall`s removed (`KnowledgeBase`'s `simplified_expr`), and
`impl_elim` strips a premise that *is* a `forall` the same way, blocking the fresh variables
as eigenvariables (§0). But a `forall` that is only one *part* of a conjunctive premise —
"induction"'s step `∀ $n ∈ Nat (… ⇒ …)` next to the base case — was compared with its
quantifier still on, so it could never match a separately proven step (only a single fact
holding the whole conjunction worked). `match_all_theory` now strips such a part too and
blocks its fresh variables as domain, exactly as `impl_elim` does, so a specific instance
still can't stand in for the universal statement. Regression:
`proofs/soundness/forall-premise-in-conjunction-needs-generic-fact.kurt` (`Q c` does not
satisfy `forall $x (Q $x)`; `forall $y (Q $y)` does).

### 8.2 More decompositions for `sub $x $a %A`

`all_single_hole_decompositions` (the candidates for `%A` and `$a`) now also yields
(a) each group of two or more, but not all, arguments of a `flat` node as one hole (any
subset if `sym`, consecutive ranges otherwise), and (b) each subterm occurring more than once
(except a bound variable) as one hole at all its occurrences. Each candidate still satisfies
`expr == sub $x $a %A` up to flattening/sorting, which only use the declared associativity
and commutativity, and still goes through `bound_var_safe`. Candidates whose hole cuts into a
binder's condition (e.g. the `∈` of `∀ $k ∈ Nat`) are now skipped rather than raising an
`EvalError` from `free_bound_vars` (a pre-existing crash). Substitution results
(`trigger_sub`, `generate_one_combination`) are normalized again (`normalize_expr`) so that
e.g. `a + (b + c)` compares equal to the typed `a + b + c`. Regressions:
`proofs/debug/flat-group-rewrite.kurt`,
`proofs/natural-numbers/induction-several-occurrences.kurt`,
`proofs/debug/quantifier-condition-not-a-subterm.kurt`.

### 8.3 `equal_expr` compares the arguments of `sym` operators as a multiset

`symmetrize_all` sorts by `canonical_key`, which depends on bound variables' *names*, so two
alpha-equivalent terms could be sorted differently and compare unequal (this surfaced once
substitution results were re-sorted, §8.2). `equal_expr_alpha` now matches the arguments of a
`sym` operator as a multiset — sound, since the operator is declared commutative. `=` and
`iff` (`SYM_KEEP_ORDER`) keep comparing in order, as they are never sorted either.

### 8.4 `calc on` as an inference rule

With `calc on`: (a) a comparison of two numeric literals (`3 <= 4`) is proven "by calc" when
it holds, (b) a claim is proven from a fact when both compute to the same normal form
(`calculate_normalized`), and (c) substitution results are computed as well (§8.2). Each
step only replaces literal arithmetic by its value, so it preserves truth under the intended
meaning of the numerals and `+ - * / ^ < <= …`; like `calc` itself, it presumes these symbols
carry that meaning (`load arith`). A false comparison (`2 = 3`) is simply not derivable.

### 8.5 Bug found and fixed: declarations could change the meaning of packaged operators

`flat`, `sym` and `chain` are claims (associativity, commutativity, transitivity), but they
checked neither whether the operator was already used nor where it came from: after `load
arith`, `sym -` made `a - b = b - a` derivable, and `chain ≠` generated the "transitivity"
`$a ≠ $b and $b ≠ $c implies $a ≠ $c`, which derives `a ≠ a` from the true facts `a ≠ b` and
`b ≠ a`. Now (a) `flat`/`sym` are rejected for an operator already used in a formula (like
`bool`/`brackets` already were), and (b) the symbols declared by a trusted theory file (packaged,
or via `-p`) are frozen (`KnowledgeBase.frozen`, filled in `load_file`; the core's symbols are
frozen in `initial_kb`): other files can't declare them `flat`/`sym`/`nonassoc`, and a `chain`
from another file may only put frozen operators first and in an order their theory already
chains them in (`check_chain_not_frozen`) -- so its generated conclusions only ever use the
file's own operators. In addition, packaged theories can't be shadowed by a local file of the
same name, and `def` only accepts `=`/`iff` from the packaged `equality.kurt`/`prop.kurt`,
since a definition is conservative only if they are reflexive. Regression:
`proofs/soundness/frozen-operators-cannot-be-changed.kurt`.

### 8.6 `use` inside proof blocks, and `--strict`

`use` inside `proof`/`assume`/`case`/`let`/`pick` is rejected: `assume A` with `use B` inside
used to close as `A implies B` "by impl-intro", a seemingly proven fact that rests on an
unproven axiom. It stays allowed at a file's top level and inside `sandbox`/`expect`, whose
content is discarded (`block_forbidding_use`). With `--strict`, untrusted files may not contain
`use`, `todo` or `chain` at all, so a checked file is proven entirely from trusted theories.
What `--strict` doesn't cover: the trusted theories themselves (their axioms are trusted by
definition), and statements that are safe by construction (`def`, syntax declarations for new
operators). Regressions: `proofs/debug/use-not-allowed-in-proof-blocks.kurt`,
`tests/test_strict_mode.py`.

### 8.7 Bug found and fixed: set.kurt was inconsistent, and had an unsound axiom

`set.kurt` had an unrestricted comprehension `{ $z | P }`, so Russell's set `{ x | x ∉ x }`
could be defined and `false` derived in about ten lines -- after `load set`, everything was
provable. It now follows Zermelo-Fraenkel set theory in a small version: separation
`{ $z ∈ $A | P }` only forms subsets of a given set (for Russell's set that only shows `R ∉ A`),
and the empty set, unions, power sets and function spaces are given by their own axioms;
`in-intersection` is now proven from the definition of `∩`. Separately, the axiom
`use $A ⊂ $B ≡ $x ∈ $A implies $x ∈ $B` had a free `$x` on its right-hand side, so a single
`c ∉ A` gave `A ⊂ B` for any `B`; it was redundant next to the correct `def` with `∀` and is
gone. Regressions: `proofs/soundness/russell-set-cannot-be-formed.kurt`,
`proofs/soundness/subset-needs-all-elements.kurt`.

### 8.8 Matching `sub`: generate candidates, then check each one

Matching a formula `G` against `sub $x a A` (find `a`, `A` with `G == A[$x := a]`) used to
accept candidates as they were constructed, trusting the construction. A random round-trip test
(`tests/test_sub_matching.py`: build `A` with holes, pick `a`, compute `G`, match `G` back)
found a candidate that isn't a decomposition at all -- the hole in a binder's own slot,
`forall $x (...)`, with `a` left unconstrained -- which the old `bound_var_safe` pre-check let
through; and gaps: no solution for a structured body with an unknown `a` (`sub $x $a (R $x d)`),
nor for a known body with an unknown `a`. Now `sub_solutions` generates candidates (all
decompositions of `G`, or, for a known `A`, every subterm of `G` as `a`) and `sub_holds` checks
each one by computing `A[$x := a]` with the same capture-avoiding substitution used everywhere
else, normalizing, and comparing with `G` -- so the generator can only make matching slower or
incomplete, never unsound. Nested `sub` is no longer allowed in axioms (it never matched in a
conclusion anyway); a rule about two variables is applied once per variable.

### 8.9 Bug found and fixed: a rule variable could depend on a `forall` premise's variable

A premise `forall $x ...` is searched with a fresh variable `v` for `$x`, blocked as domain so
that it can't be assigned. But nothing kept *other* variables of the rule from taking a value
containing `v`: with the fact `$a ^ 1 = $a`, the premise of `(forall $x ($x = $T)) implies Q`
was satisfied by `$T := v ^ 1` (since `v = v ^ 1`), so `$T` depended on `$x` after all and `Q`
followed -- although "some term equals every x" holds only in a one-element domain. This is
older than this week's changes (it also happens at commit `79604ef`). Now such variables are
also recorded in `State.eigen` (`block_eigen`), and a non-boolean variable of the rule (the
pattern side) can't take a value containing one; a boolean `%A` may (it is *meant* to depend on
`$x`, as in "forall-elim"), and so may the variables of a fact (the other side), since a
universal fact may be instantiated at the fresh variable. Regression:
`proofs/soundness/forall-premise-fresh-variable-stays-generic.kurt`.

### 8.10 Non-boolean binder bodies that depend on the bound variable

For sums (and later `max`, `sup`, `lim`), an axiom must be able to talk about a summand `$T`
that depends on the bound variable. Letting every `$T` capture it would change what existing
axioms mean (in `(forall $x ($x = $T)) and (P $T) implies Q`, `$T` is one fixed term). So only
a variable that occurs exclusively as the *whole* body of binders over the same variable, or as
the body of `sub` for it, may (`find_dependent_vars`, recorded in `dependent_vars` when a
formula is stored, checked in `may_capture`): such an axiom only ever uses `$T` for the bound
variable or with something substituted for it, so the dependence is what it means. Being just
somewhere inside the scope isn't enough -- the first version allowed that, and the stored fact
`exists $y (not ($x = $y))` (from `forall x (exists y (not (x = y)))`) then gave `exists y (not
(y = y))`; `capture-avoidance-blocks-unsound-instantiation.kurt` caught it. Regression:
`proofs/soundness/dependent-summand.kurt`.

### 8.11 Quantifiers with a condition: rules instead of a hard-coded rewrite

`remove_outer_forall_quantifiers` used to rewrite a stored or claimed `∀ (cond) body` into an
implication `cond ⇒ body` with a fresh variable. That made conditioned `∀` work, but only `∀`:
there was no way to say what a condition means for any other binder (`∃ $d > 0 ...` had no
exists-intro at all, and `lim $x > 0 a T` couldn't be defined). Now a condition is just part of
the formula, and rules say what it means: in a rule, a binder `sub $x $v %C` stands for any
condition on the bound variable `$v` (`unpack_condition`), and logic.kurt has
"forall-cond-elim", "exists-cond-intro", "forall-cond-def", "exists-cond-def".

Matching (`sub_condition_match`): an expression's binder with condition `C` on its bound
variable `y` matches `sub $x $v %C` with `%C := C[y := $x]` -- *every* occurrence of `y` becomes
the hole, so the match is unique (no search), and `%C` never contains the bound variable, which
could otherwise escape its binder when the rule substitutes another value for `$x`. The body is
renamed from `y` to `$v`, which is blocked like any pattern binder. Three safeguards:

- a rule can use `%C` only as `sub $x ... %C` with the same hole (`check_condition_holes`),
  since on its own `%C` would mention the rule's `$x` -- e.g. `(∀ (sub $x $v %C) %P) ⇒ %C`
  would give `$x > 0` for any `$x`;
- an instance whose binder lost its bound variable -- e.g. `%C := 5 ∈ Nat` from a decomposition
  of `5 ∈ Nat ⇒ P 5` without a hole -- is skipped (`valid_bindop_conditions` after
  `trigger_sub`, in `impl_elim` and `match_all_theory`), not stored or crashed on;
- a binder with a condition never matches one without.

`all_theory` used to yield the body of a stored outer `forall` as a separate fact; that loop was
dead code while every outer `forall` was stripped on storing, but would have yielded the body of
a conditioned one *without its condition*, so it was removed. `unpack_condition` now counts
distinct variables, so a condition may mention its variable twice (`$x > 0 ∧ $x < 1`).
Regression: `proofs/soundness/conditioned-quantifier-rules.kurt` (conditions can't be dropped,
weakened, swapped, or leaked; no capture in the body).

The cost: `∀ $x ∈ A (x ∈ B)` (from `let x ∈ A`) and `∀ $c ($c ∈ A ⇒ $c ∈ B)` (the definition of
`⊂`) are no longer identified silently -- one "forall-cond-def" step connects them
(`proofs/mafi1/001-two-equal-sets.kurt`, `proofs/natural-numbers/induction.kurt`).

The functions of `analysis.kurt` (`lim`, `sup`, `max`, ...) give a value for every argument, so
it has only introduction rules: `(lim $v $a $T) = $L ⇔ ε-δ` would, by reflexivity of `=`, prove
ε-δ for limits that don't exist. And "lim-cond-intro" needs `$a` to be approached by values with
the condition; otherwise ε-δ holds vacuously for every `$L`, and two limits would prove `5 = 6`
(`proofs/analysis/limit-with-condition.kurt`).

### 8.12 Bug found and fixed: renaming a bound variable nested a binder's arguments

`alpha_rename_binder_body`, under an inner binder with a condition, rebuilt it as
`[op, cond, [args...]]` instead of `[op, cond, *args]`, so `sum x (0, n) x` became
`sum x ((0, n) x)`. Nothing reached it before a binder with a condition (`∀ $n ∈ Nat`) had a
multi-argument binder (`sum`) in its body -- gauss.kurt, once the conditioned `∀` was no longer
turned into an implication. It made matching fail (a false rejection), not succeed.

### 8.13 Bug found and fixed: a chain's continuation line used its own operator

`get_chain_op` is meant to return the strongest operator of a chain so far (kurt-doc.md §4.6),
but returned the last one, so the continuation rows `a = b`, `< c`, `= d` claimed `a = d`
instead of `a < d`. The claim then simply failed to derive (a false rejection, not a false
proof). Regression: the end of `proofs/arithmetic/chains.kurt`.

### 8.14 The comma is right-associative, not flat

The comma used to be `flat`, so `(x, (y, z))`, `((x, y), z)` and `(x, y, z)` were one and the same
expression. That's harmless for argument lists, but makes a theory of pairs unsound: the natural
axiom `($a, $b) = ($c, $d) ⇔ $a = $c ∧ $b = $d` would give `x = (x, y)`, with `$a := x`,
`$b := (y, z)`, `$c := (x, y)`, `$d := z`. Now the comma is right-associative (`infix , 5 4`): a
triple is the pair `(a, (b, c))`, as in set theory, and set.kurt's "pair-eq" is sound. Lists of
formulas (`use A, B, C`) and of arguments (`g(a, b, c)`) follow the right-nested commas.
Regression: `proofs/soundness/tuples-are-nested-pairs.kurt`.

### 8.15 Bug found and fixed: the variables of an assumption counted as "for all"

An assumption was stored like any fact, so its free variables meant "for all": inside
`assume P $x`, `P $y` followed, closing gave `P $x ⇒ P $y`, and then from `P c` anything like
`P d` (the same with `assume %A`, which made every proposition true inside the block). This is
old, older than the kernel -- and the kernel didn't catch it, since it shared the wrong reading:
a wrong rule of the logic, not a wrong implementation, which search and kernel can't catch for
each other. Now the free variables of an assumption are fixed in its block (`fixed_vars`,
`is_var`): neither renamed nor instantiated, and variables again once the block is closed.
`proofs/natural-deduction/contraposition.kurt` had relied on it (its `assume A` stood for every
proposition, with a warning saying so); it now uses the excluded middle, as it should.
Regression: `proofs/soundness/assumption-variables-are-fixed.kurt`.

## 9. The kernel: every step is checked again

The search (unification, `sub` matching, stripping quantifiers, blocked and eigen variables,
dependent variables) is where almost all the bugs above were. So each step it accepts comes with a
*certificate* (`Certificate` in kurt.py), which the kernel (`kernel_verify`) checks on its own,
without any search:

- the rule is in the theory (or is one direction `L ⇒ R` of an `iff` there), and so is each fact;
- the rule's outer `∀`s are stripped with the recorded fresh names (for the premise also in the
  conclusion);
- the values are filled in *without renaming*: a value may contain a variable that is bound where
  the variable occurs only if that is meant -- a boolean `%A` may, a non-boolean `$T` only its own
  bound variable (`k_dependencies`, the criterion of §8.10, written again) -- then `sub` is
  evaluated with the kernel's own capture-avoiding substitution, and a condition `sub $x $v C` in a
  binder must not contain `$v` (§8.11);
- the instance of the conclusion is the goal, and the instance of the premise consists of instances
  of the facts (a conjunct, a group of flat conjuncts, or the body of a `∀` with a recorded fresh
  name);
- the eigen condition: the fresh names of `∀` premises get no value, and no non-boolean variable of
  the rule depends on them (§0, §8.9); the free variables of the goal get no value.

Besides its own code, the kernel trusts the parser, `unpack_condition` (which variable a binder
binds), `normalize_expr` (`flat`, `sym`, `calc`), and `equal_expr` (renaming of bound variables;
for the kernel, `=` and `iff` compare in either order, since they are `sym` but keep their order
for `def`). Also `top-intro`, `calc` steps, and `todo` have certificates.

The kernel checks every step, always. A step it rejects doesn't count: `KernelError` stops a file
(in the shell, only that line fails), and no `expect` can catch it. A rejection means that the
search and the kernel disagree -- a bug in one of them (so far, both disagreements found were the
kernel's: `=`/`iff` in either order, and a fact covering several flat conjuncts). So every step of
every proof file, theory and tutorial lesson in the test suite is checked by the kernel too. `tests/test_kernel.py` changes real certificates (no facts, another goal, a
rule not in the theory, a value for a goal variable, a value depending on a fresh variable, a
capture; for blocks: another result, no `∀`, not the last line, a witness that escapes) and
checks that the kernel rejects each one.

Closing a block has a certificate too, checked with the block's level (`kernel_verify_block`):

- impl-intro (`assume`, `case`): the result is `assumption ⇒ last line`;
- not-intro: the last line is `false`, the result `¬ assumption`;
- forall-intro (`let`): the result is the last line under the `∀`s of the `let`, each of whose
  variables was new in the block;
- exists-elim (`pick`): the fact about the witness is the body of the existential fact it was
  picked from, with the witness (new in the block) for the bound variable, and the result is the
  last line;
- and for each: no individual constant of the block occurs in the result.

`.kurtc` files store the certificates of a checked file, to skip the search the next time: each
stored certificate is rebuilt against the facts as they are then (its canonical names aligned
with the current goal, rule and facts), and has to pass the kernel; otherwise the search runs.
A forged `.kurtc` (`tests/test_kurtc.py`: the right hash, a certificate claiming `B` from `A` and
`B ⇒ A`) is rejected by the kernel, and the claim then fails as it should.

Open design question: when may a schema variable depend on a bound variable -- today by the criterion of
§8.10; the alternatives are to declare it in the rule (like Isabelle's `?T i`) or Metamath's
distinct-variable conditions.

## How to extend this

New adversarial cases belong in `proofs/soundness/`, following the existing
files' pattern: a comment explaining what property is being tested and why
it matters, then either a `;;; ` marker (required for anything that fails
while *closing* a block — `expect`, per its documented limitation in
`kurt-doc.md` §9.6, cannot observe that) or `expect "KIND"` (for a failure
from an ordinary statement). Update this file alongside any new finding.
