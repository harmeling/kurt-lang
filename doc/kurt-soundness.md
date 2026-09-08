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
- **`equal-elim`-driven substitution doesn't re-flatten into a `flat` operator's
  argument list** — found while writing a real test proof for `arith.kurt`'s
  new factorial recursion (`proofs/arithmetic/factorial-recursion.kurt`).
  Chaining a *second* application of "factorial-step" (to go on from `1! = 1`
  to prove `2! = 2`) reliably failed: substituting a fact whose RHS is itself
  a `*`-expression (`1! = 1 * 1`) into another `*`-context (`2 * 1!`)
  produces some structural shape that doesn't `equal_expr`-match a naturally
  *typed* target (`2 * (1 * 1)`, which flattens to a 3-argument `2 * 1 * 1`
  at parse time) — even though both denote the same flattened multiplication.
  Confirmed this is specifically about the substituted value re-using the
  same `flat`/`sym` operator as its context (substituting a bare-literal RHS,
  as `factorial-base`'s `0! = 1` does, works fine at any nesting depth tried).
  This is a completeness gap, not a soundness one — it can only make a true
  goal harder to reach in one step, never make a false one derivable — but
  it's a real limitation of the matching engine, not (as far as tested) a
  bug in any specific theory. Not investigated further here; worth a
  dedicated look at wherever `apply_subst`'s substitution result is compared
  against a `flatten_all`-processed target, next time someone works on
  `derive_expr`/the matching engine rather than on theory content.

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

Once the crash was out of the way, `natural.kurt`'s induction axiom
itself checked out as functionally correct — `(P 0) and (forall $n in Nat
(P $n implies P ($n+1)))` derives `forall $n in Nat P $n` via one
`impl_elim` step, as expected. The ergonomic catch (not a bug): the base
case and step must be phrased as a single conjunction, not two separate
`use` facts, since `impl_elim` only does one hop and needs the whole
antecedent to match at once — the same single-hop limitation already
noted in §6.1, not something specific to this axiom.

## How to extend this

New adversarial cases belong in `proofs/soundness/`, following the existing
files' pattern: a comment explaining what property is being tested and why
it matters, then either a `;;; ` marker (required for anything that fails
while *closing* a block — `expect`, per its documented limitation in
`kurt-doc.md` §9.6, cannot observe that) or `expect "KIND"` (for a failure
from an ordinary statement). Update this file alongside any new finding.
