# What can't be expressed in Kurt (yet)

**Scope.** Kurt lets a theory file act as a *metalanguage*: declare a sort, declare some symbols
into it, state axioms about them as ordinary Kurt formulas, and you have an embedded *inner*
language with its own judgments, rules, even its own binders (`modal.kurt`, `lambda.kurt`,
`set.kurt`'s ordered-resources experiment in `dev/deep-logic-experiments.md`). That mechanism is
more general than it first looks, and it's easy to either overestimate what it needs (assume some
feature is missing when it's really just an axiom nobody wrote, or a cleverer use of what's already
there) or underestimate it (assume deep embeddings are a closed, solved problem). This note tries
to say precisely, with the code to back it up, where the real boundary is.

**How this note was written.** Every claim below was tested directly against Kurt, not reasoned
out in the abstract — §2.3 in particular records three successive hypotheses about "the" blocker
for `lambda.kurt`'s general theorems, two of which turned out to be wrong when actually tried. The
retractions are kept in, on purpose: the thing worth trusting here is the empirical trail, not any
one paragraph's confidence.

Companion reading: `dev/deep-logic-experiments.md` (the experiments this grew out of),
`dev/todo.md` #22 and #36 (the open backlog items), `doc/kurt-ref.md` §8.2 (the theories, including
`lambda.kurt`), `doc/kurt-spec.md` §3 and `doc/kurt-soundness.md` (what Kurt's logic actually
guarantees).

## 1. The general mechanism isn't hard-coded to anything

`natural.kurt`'s induction axiom looks like special support for `Nat`:

    use ((sub $x 0 %A) ∧ (∀ $n ∈ Nat (sub $x $n %A ⇒ sub $x ($n+1) %A))) ⇒ ∀ $n in Nat (sub $x $n %A)   "induction"

It isn't. `%A` is Kurt's ordinary formula-schema-variable device, the same one every rule of
`propositional.kurt`/`logic.kurt` uses; `sub` is the same substitution operator used everywhere else. Kurt's
matching/search instantiates `%A` by ordinary unification when the axiom is applied — nothing in
`kurt.py` knows this particular axiom is "about" natural numbers. The *only* thing specific to
`Nat` is the mathematical content of this one `use` line.

**Why a `%`-variable at all, rather than an ordinary object-level variable?** Because induction is
a claim about *every property*, not about any one object. `doc/kurt-spec.md` §3.1 is explicit that
a symbol beginning with `$` stands for a term and one beginning with `%` for a formula — these are
genuinely meta-level devices of Kurt itself (the host language), not features of whatever object
theory is being axiomatized. An ordinary `$`-variable can't play this role: it ranges over
*individual terms*, and "holds for every term that satisfies this property" needs a variable that
ranges over *properties*. This is not particular to `Nat`'s induction — `and-elim`, `or-elim`,
`forall-elim`, every rule that must apply uniformly to "any fact of this shape," needs exactly the
same meta-level device, with or without an inductively-defined sort anywhere in sight.

**Consequence:** anyone can write an analogous structural-induction axiom for *any* sort whose
constructors are closed and don't involve a Kurt-level bound variable. For a sort with closed
first-order constructors `leaf` and `node L R`, for instance:

    use (%A leaf) ∧ (∀ L R ((%A L) ∧ (%A R) ⇒ %A (node L R))) ⇒ ∀ T (tree T ⇒ %A T)   "tree-induction"

is available today, zero changes to Kurt needed. (`lambda.kurt`'s own `term` sort turns out to need
one extra step first before the same recipe applies cleanly to it — see §2.2.) Nobody has written
such an axiom for most theories; that's a theory-file gap, not a language limit. Section 2 is the
one actual limit found so far.

## 2. The one real limit: induction or generalization over a binder borrowed from Kurt itself

### 2.1 Two ways to represent an object language's own binder

- **First-order (reified):** de Bruijn indices, or named variables with explicit contexts and
  explicit freshness side-conditions. The bound variable is ordinary first-order data; no real
  Kurt binder appears in the representation. `lambda.kurt`'s `abs A M` is this: `M` is just a
  subterm, nothing is captured.
- **Higher-order (HOAS):** use Kurt's *own* `bindop` to stand for the object binder. `lambda.kurt`'s
  named `λ x M` does this. The payoff is real: alpha-equivalence and capture-avoiding substitution
  come for free from Kurt's own matching and `sub`, with no hand-written de Bruijn machinery.

`lambda.kurt` uses both at once, and that's the tell. The named `λ`'s own header says why it stops
short of a fully general typing rule: *"the current pure-Kurt rule language does not express the
full hypothetical premise of named abstraction conveniently."* The same wall blocks induction, for
the same reason.

### 2.2 A complication found by testing it: the two encodings currently share one sort

Before asking whether the de Bruijn side can get general theorems "for free" (§1's recipe), check
what `term` actually contains. Testing it directly:

    load lambda
    app (λ x x) (abs base (at zero))   ; mixes a named λ-term and a de Bruijn term as app's two args

raises no sort error. Compared with an actual violation:

    app base unit                      ; `base` has sort `type`, not `term`
    TypeError: arg number 1 of `app`, i.e., `base` must have sort `term`

confirms the checker is active and genuinely accepts the mix: `λ x M` and `abs A M` are both just
`term`-sorted constructors of *the same* sort, freely interchangeable as subterms of each other.

That means the induction axiom suggested for `lambda.kurt` in the previous version of this note —

    use (∀ n (%A (at n))) ∧ (∀ A M (%A M ⇒ %A (abs A M))) ∧ (∀ M N ((%A M) ∧ (%A N) ⇒ %A (app M N))) ∧ (%A unit)
      ⇒ ∀ M (term M ⇒ %A M)

is **false as written**, not merely incomplete: it claims to cover every `term`, but `λ x x` is a
`term` not covered by any of its four premises. Asserting it anyway would be asserting an unsound
axiom — the real constructor list of `term`, as currently declared, is `at`, `abs`, `app`, `unit`,
*and* `λ`.

So there's a prerequisite, not yet done, before §1's recipe can even apply here: `lambda.kurt`
would need to stop sharing one sort between the two encodings — either give the de Bruijn
constructors their own sort (say `dterm`, with `λ` deliberately excluded from it), or keep one sort
and add an explicit "is a pure de Bruijn term" predicate, proved preserved by every rule used. Both
are ordinary, first-order theory-engineering — real, somewhat fiddly work, but not blocked by
anything.

### 2.3 Three hypotheses tested, in order — this section's history

The first version of this note claimed the blocker was that `%A` would need to range over
*functions* term→term, like Abella's `∇`. That claim was tested directly and does not hold up.
What actually happens is more specific and more interesting, and the only way to find it was to
keep testing each new guess against Kurt itself rather than reasoning further from the armchair.

**Hypothesis 1 (wrong): plain structural induction over a binder-containing sort is impossible.**
Tested directly: a toy sort with a nullary `leaf` and a real binder `lam $x M`, with a structural
induction axiom covering both constructors —

    use (sub $subj leaf %A) ∧ (∀ $x ∀ M ((sub $subj M %A) ⇒ (sub $subj (lam $x M) %A))) ⇒ ∀ $subj %A

— is accepted without complaint. `M`, once pattern-matched out of `lam $x M`, is an entirely
ordinary schema variable; nothing about induction over the raw *shape* of a term needs to know
that `lam` also happens to bind a variable for other purposes. Retracted.

*Correction (2026-10-20, todo 44, §2.5):* accepted, yes -- but it is not a structural induction
for `lam`: by Kurt's own reading of a schema variable under a binder, its `lam` case covers only
bodies that don't depend on `$x`, and with the obvious no-confusion axioms the rule proves `false`.
The hypothesis "induction over a binder-containing sort is impossible" stands, for a Kurt binder.

**Hypothesis 2 (real, but narrower than it looked): nested `sub`.** Properties that are *shape*-only
work by hypothesis 1, but the preservation/confluence-relevant properties need to relate a term to
a substituted version of itself, and composing two substitutions in one expression is explicitly
refused:

    use (sub $x $T (sub $y $N M)) = (sub $y (sub $x $T $N) (sub $x $T M))   "subs-commute"
    EvalError: nested `sub` is not supported -- write a rule for one variable, and apply it once per variable

and `sub` cannot even appear in a `show`/goal line at all (`EvalError: `sub` is only allowed in
`use` and `def`, to write axiom schemas`) — so this specific fact, "substitutions commute," can be
neither asserted nor posed as something to prove, in its general form. This matters for some
confluence-style arguments. It turns out **not** to be what blocks the main substitution lemma
needed for preservation, though: that lemma only ever needs one `sub` per step (substitute into a
strictly smaller subterm, cite the lemma on that subterm, wrap the result in an ordinary,
non-`sub` constructor) — and stating it directly parses and type-checks with no nesting complaint:

    use ((has (extend Γ A) M B) and (has Γ N A)) implies (has Γ (sub x N M) B)   "substitution-lemma"

So nested `sub` is a real, narrower restriction (relevant to a specific class of facts that relate
two substitutions to each other), not the thing standing between `lambda.kurt` and preservation.

**Follow-up (todo #37, closed 2026-10-17): does confluence need it either?** Not via the standard
modern route. Confluence (Church-Rosser) is normally proved through a parallel-reduction relation
`⇉` and its diamond property, whose one substitution-shaped lemma is *substitutivity of parallel
reduction* — "if `M ⇉ M'` and `N ⇉ N'` then `sub x N M ⇉ sub x N' M'`" — a single `sub` on each
side, never nested (the critical beta/beta overlap case substitutes once, with the
already-available `M'`/`N'`, not twice into one term); this shape type-checks fine in Kurt. The
classical "substitutions commute" lemma (Barendregt 2.1.16) is real, but it's a prerequisite only
for an older proof strategy (simultaneous substitution built by iterating single substitution, or
direct reduction-diagram chasing without a parallel-reduction relation) — not for the
parallel-reduction route, and not for preservation. No real proof surfaced that needs nested `sub`
for either of todo #22's two actual target theorems; the restriction stands as is.

**Hypothesis 3 (the one that held up): a schema variable can't be both a binder's own bound-name
*and* an ordinary argument elsewhere in the same rule.** This is what `lambda.kurt`'s own header
means by "the current pure-Kurt rule language does not express the full hypothetical premise of
named abstraction conveniently" — tracked down to a specific, reproducible mechanical cause.
Attempt the fully general named abstraction rule the de Bruijn encoding already has, but for named
`λ`, with an explicitly-named context `extendx Γ x A` ("Γ extended with x:A"):

    use (has (extendx Γ x A) M B) implies (has Γ (λ x M) (fun A B))   "named-abstraction-general"

This is *accepted* — no error at declaration time. But it cannot actually be *used*. Given the
exact fact its premise needs, already proved two lines earlier —

    has (extendx empty p A2) (λ q p) (fun C A2)
    has empty (λ p (λ q p)) (fun A2 (fun C A2))
    ProofError: can not derive `has empty (λ p (λ q p)) (fun A2 (fun C A2))`
    - `named-abstraction-general` (line 11): missing `has (extendx (extendx empty p A2) x2 C) p A2`

Kurt's search *did* try the rule — but it asks for the missing premise using the rule's own literal
bound-name (`x2`, from how the axiom was written), not `q` (the actual bound name in the goal,
`λ q p`). The binder's own slot (`λ x2 M`) got correctly matched against the goal's `q` for
alpha-equivalence purposes; the *separate* occurrence of the same schema-variable name as an
ordinary argument to `extendx` did not follow along. The two occurrences of "x2" are unified
independently and end up desynchronized.

This is not a guess about internals — `kurt.py` documents exactly this class of problem, for the
mirror-image case, with its own fixed bug: `(forall $x %A) implies (sub $x $a %A)` ("forall-elim")
needs `$x` kept in sync between the *premise*'s binder and the *conclusion*'s use of the same name,
and an earlier version of the renaming code got this wrong (`doc/kurt-soundness.md`'s writeup of
the `impl_elim` bug — the comment at the fix: *"renaming must be applied identically to both sides
to keep them in sync... silently generated a fresh name for the premise's own copy of `$x` that
then went unused"*). That fix handles *a bindop's own slot, reused inside a `%`-schema via `sub`,
between premise and conclusion*. It does not cover *a bindop's slot in the conclusion, reused as an
ordinary (non-`sub`, non-bindop) argument in the premise* — the exact shape a named hypothetical
context needs (`extendx Γ x A`, where `x` must be *the same x* as the `λ x M` it licenses).

### 2.4 The exact code, and why the obvious fix is not obviously safe

Traced to the line. When the conclusion's `λ x2 M2` is matched against a goal's `λ q p`
(`unify_exprs_with_patterns`, the bindop-matching case):

    # Rename the expr-side binder body from v_e to v_p (alpha-eq) before unifying -- ...
    args_e = alpha_rename_binder_body(args_e, v_e, v_p, kb)
    for s_middle in unify_exprs_with_patterns(list(zip(middle_e, middle_p)), s, kb):
        # Block the pattern binder (domain+range) during descent
        s_local = s_middle.block_always(v_p)
        yield from unify_exprs_with_patterns(list(zip(args_e, args_p)) + tail, s_local, kb)

`v_p` is the rule's own bound-name (`x2`); `v_e` is the goal's (`q`). The goal's body is rewritten
to use `x2` (not the other way around), and then `x2` is **blocked** (`block_always`: added to both
`blocked_as_domain` and `blocked_as_range`) — meaning it may never be assigned a value by
unification — before matching continues into `tail`, which carries the *rest of the whole rule's
matching problem forward*, premise included. There is no matching `restore_blocked` call anywhere
in this branch (contrast `match_against_sub`, which does call `restore_blocked` after it's done
with a `sub`-bound name, lines 7025/7069). So `x2` stays permanently blocked, unassignable, for the
rest of the proof step — which is exactly why the premise comes back asking for `x2` verbatim
rather than `q`: `x2` was never bound to `q` at all, by design, since the whole point of
`block_always` is to keep the rule's bound-name standing for "any" value, never a specific one.

That "stand for any value, never a specific one" is not a bug — it is what makes `forall-elim`
sound, exactly documented at the comment above this code: without it, `∀ $x (Q $x $x)` could
wrongly match `∀ $z (Q $x $z)` (soundness review of 2026-09-29). A named hypothetical-context rule
asks for the opposite of what this mechanism guarantees: it wants `x2`'s *one specific value in
this application* (`q`) to be visible and usable elsewhere in the same rule, not kept generic. Put
plainly: the rule needs one name to behave as *both* "a bound name that must stay generic, so the
binder-matching stays sound" and "a schema variable whose concrete value this application should
expose" — two roles Kurt's matcher deliberately keeps separate, for a reason with its own
soundness incident on record.

That reframes the limit, again. It is not that Kurt's logic is missing an *order* of quantification
(`∇` as literally "a variable ranging over functions") — hypothesis 1 seemed to show induction over a
binder-containing sort is fine (§2.5: it isn't), and the basic substitution lemma shows single-`sub`
reasoning is fine too. It is this specific role conflict, for which `∇`/contextual variables are precisely the
devices other systems built: a second kind of binding (Abella's `∇`, distinct from `∀`) whose own
proof rules are designed to let a "generic" name's identity travel safely to other parts of a
derivation, which is exactly the missing piece here.

**The obvious engineering fix was attempted (2026-10-17) and found unsafe, concretely, not just
in principle.** The change: block `v_p` only while matching the binder's own body (`args_e` vs
`args_p`), then leave its scope (a new `unblock_bindop_scope`, mirroring `trigger_sub`'s local
`unblock_as_before`) and bind it to `v_e` before continuing into `tail`. Tried against the
`named-abstraction-general` example from §2.3 step by step:

- The *simple* case (the inner application, where the body doesn't itself mention the bound name)
  started working: the search asked for the premise using `q`, the goal's actual name, not `x2`.
- The *general* case (the outer application, where the body is itself `λ q p` — genuinely
  mentioning the outer bound name) still failed, for a **second, separate** reason: binding the
  body-pattern variable (`M2`) to a value that contains the now-blocked `x2` is refused by an
  existing, unrelated safety check, `may_capture`/`contains_blocked_as_range`. That check exists
  for a *different* pattern (`dependent_vars`, populated by `find_dependent_vars` for things like
  `sum $i ($a, $b) $T`, where `$T` is *only ever* the whole body of or strictly inside a binder
  over `$i`) and explicitly does not cover a variable that *also* occurs free, outside any binder,
  elsewhere in the same rule (the premise) — exactly the named-hypothetical-context shape. So the
  one-line fix above is not sufficient even for the case it was aimed at; a real fix would need to
  extend `find_dependent_vars`/`may_capture` to recognize this second dependency pattern too, a
  materially bigger, second change to the same soundness-sensitive machinery.
- Before investigating that second layer further, the existing adversarial regression suite was
  run against the (partial, already-incomplete) first change: `proofs/soundness/search-bugs-the-kernel-caught.kurt`
  — one of the exact tests written to catch this bug class (the `∀ $x (Q $x $x)`/`∀ $z (Q $x $z)`
  capture from the 2026-09-29 review) — **crashed with an `AssertionError`** inside
  `unify_exprs_with_patterns` (`assert s.lookup(v) is None`, hit when matching `tail` after the new
  binding). Not a subtle false positive — an outright crash, on the first existing regression test
  that exercises this code path adversarially.
- The change was reverted immediately (`git checkout -- src/kurt/kurt.py`) and the crash confirmed
  gone; the full suite is back to its clean 549-test baseline.

So this is now a tested, not merely argued, conclusion: the obvious fix is unsafe, and the problem
has at least two layers (the renaming/correlation issue in §2.3, and a second, independent gap in
`dependent_vars`/`may_capture`), not one. Nothing was committed from this attempt except this
write-up.

**What isn't blocked.** The de Bruijn encoding sidesteps this entirely: `abs A M` has no real Kurt
binder in it at all, so there is no bound-name/ordinary-argument correlation to get wrong, and §1's
induction recipe (once §2.2's sort split is done) works without anything new. The practical
pattern, already implicit in how `lambda.kurt` is written: state and prove general theorems
(preservation, confluence) over the de Bruijn representation only; keep named `λ` strictly as
reader-facing sugar for closed, concrete example terms, where each instance is checked directly
rather than derived from a general named rule.

**What it would take to lift this properly.** At minimum: (1) the `unblock_bindop_scope` change
from this attempt, (2) a second change teaching `find_dependent_vars`/`may_capture` to recognize a
variable that is both "the whole body of a binder" *and* separately free in an ordinary premise
argument correlated with that same binder (not just the `sum`-style "only inside the binder"
pattern), with (3) new adversarial soundness tests written *before* either change, specifically
targeting the crash found here and its variants, verified to still be rejected after. Given a
first, smaller attempt already crashed an existing regression test, a dedicated device (Abella's
`∇`, Beluga's contextual meta-variables) looks more likely to be the real route than incrementally
patching this matcher, but that is this investigation's working judgment, not a settled answer.

### 2.5 Induction over a Kurt binder is unsound as written, and the named β-step can't be reasoned about

Found while attempting preservation for todo 44 (§5). Two more reasons why general theorems about
the *named* `λ` are out of reach, both independent of §2.3's hypothesis 3.

**Hypothesis 1's induction axiom proves `false`.** Kurt reads a schema variable under a binder as
*not* depending on the bound variable, unless it occurs only under binders over it or in a `sub` for
it (doc/kurt-ref.md §4.4). In `∀ $x ∀ M ((sub $subj M %A) ⇒ (sub $subj (lam $x M) %A))`, `M` also
occurs outside `lam $x`, so the `lam` case is about bodies that don't depend on `$x` -- constant
functions -- and the conclusion claims every term. With the conclusion written so that the search
applies it (`⇒ ∀ $s (sub $subj $s %A)`, §5.5; the form `⇒ ∀ $subj %A` was never applied before 2026-10-23, §5.5) and two
no-confusion axioms, this checks:

    load logic, equality
    arity lam 2
    bindop lam
    const leaf
    use (sub $subj leaf %A) ∧ (∀ $x ∀ M ((sub $subj M %A) ⇒ (sub $subj (lam $x M) %A))) ⇒ ∀ $s (sub $subj $s %A)   "ind"
    use ¬(lam x x = lam x $c)            "identity-not-constant"
    use ¬(lam x x = leaf)                "identity-not-leaf"
    ; A(t) := t = leaf ∨ ∃ c (t = lam z c): true of leaf and of every lam x M with a constant M
    ...                                  ; (both premises proved with `let M` / `assume`)
    lam y y = leaf ∨ ∃ c (lam y y = lam z c)      ; by ind -- the identity is a constant function
    ...
    false

So the axiom says "every body is constant", not "induction over terms". A correct `lam` case needs
the induction hypothesis for an *open* body -- a generic `x`, the `∇` of §2.4 -- which an axiom
can't state. (A body that may depend on `$x` must occur only under binders over it; then the
hypothesis `sub $subj M %A` can't be written.)

**The β-step can't occur in a proof line.** `sub` is allowed only in `use` and `def`; a proof about
`app (λ x M) N ↦ sub x N M` for a generic `M` would need lines with `sub x N M` in them (the result
of the step, the witness of a diamond) -- refused. Proofs can only take concrete bodies, where the
search computes the `sub`. And the inversion of lambda.kurt's typing for named `λ` is a disjunction
over the *shape* of the body (it is `x`; it doesn't contain `x`; it is `app F x`), which is no
formula. Together with §2.3 this settles it: general theorems about named terms are not expressible;
over the de Bruijn presentation they are (proofs/classics/lambda-preservation.kurt, §5).

## 3. Not a limit: second-order logic needs nothing but `sort`

A natural question in the same spirit: quantify over individuals *and* over sets of individuals —
two sorts (`obj`, `set`), with their own quantifiers. **This is not blocked at all.** `sort obj`,
and `set.kurt`'s `℘` for "the set of all subsets of `Obj`", plus Kurt's one existing `∀`/`let`
restricted by a domain condition — exactly the device `natural.kurt` already uses for `∀ n ∈ Nat`
— gives genuine, sound, monadic second-order quantification today, with no new axiom and no kernel
change:

    let x ∈ Obj
        ...
    let X ∈ ℘(Obj)        ; ranges over every subset of Obj: this is second order
        ...

This is fully general. The question that's easy to conflate with it is narrower: not "can Kurt
quantify over sets" (yes), but "can a theory mint a **second, visually distinct quantifier glyph**
that still gets `let`'s automatic, kernel-enforced-freshness generalization for free, the way `∀`
does" — i.e. have `let x ∈ Obj` auto-produce `A1 x (...)` and `let X ∈ ℘(Obj)` auto-produce a
differently-spelled `A2 X (...)`, instead of the same `∀` both times, told apart only by the
condition written inside it.

**Elimination for a custom `A1`/`A2` is no problem at all.** `(A1 $x (%P $x)) implies (%P $t)` for
an object-sorted `$t` is ordinary schema instantiation, exactly like `forall-elim`. Two sorts, two
symbols, two elimination axioms — fine, no different from any other deep embedding.

**The automatic-introduction *convenience* is what's missing**, for two separate, code-grounded
reasons:

1. **`let`'s role lookup is a global singleton, not sort-dispatched.** `let` is the mechanism that
   turns "whatever I proved of a fresh constant" into a quantified fact, and its block-closing code
   is hard-wired to one symbol, found without ever looking at the constant's sort:

       universal = kb.role_symbol('universal')
       assert universal is not None, 'BUG: `let` is opened only with a universal quantifier'
       expr = [Token('SYMBOL', universal), condition, expr]

   `role_symbol('universal')` scans every symbol's roles and returns the *one* that was registered
   — registering a second one is explicitly refused:

       holder = self.role_symbol(role)
       if holder is not None and holder != symbol:
           raise KurtException(f'EvalError: `{holder}` is the `{role}` already -- a role has one symbol')

   (`pick`/`'existential'` is identical.) "Dispatch by sort" would mean generalizing the role map
   from role → symbol to role → {sort: symbol}, and teaching `let`/`pick`'s block-closing code to
   look up the *sort of the constant just generalized over* (which it doesn't check today at all)
   and wrap with the glyph registered for that sort, instead of the one global holder.

2. **A hand-written introduction axiom, as a substitute, would be unsound**, not just inconvenient.
   `use (%P c) implies (A1 $x (%P $x))` looks like generalization, but instantiate
   `%P($y) := ($y = c)`: the premise `%P(c)` is `c = c`, trivially true, and the axiom would hand
   you `A1 $x ($x = c)` — "every object equals `c`" — false whenever there is more than one object.
   Generalization is only sound when `c` doesn't occur in anything used to derive the property, and
   that's a fact about the *current proof state*, not something a self-contained axiom can check by
   pattern-matching alone. `let` gets away with it because the kernel tracks this directly (block
   levels, `all_fixed_vars`) and refuses to let the fresh constant escape in an assumption — an
   enforcement an ordinary `use` axiom has no way to perform.

   (This is the same family of freshness/soundness risk §2.3's "named-abstraction-general" test
   ran into — which is why both needed checking carefully rather than asserting from the armchair —
   but here Kurt already has a sound, working alternative; in §2 it doesn't, yet.)

**What isn't blocked.** The logic itself (this section's opening example) is available right now.
If a visually distinct glyph is still wanted on top of it, it can be added as *notation*, defined by
a proven equivalence to the real `∀` (the same move `modal.kurt` uses to relate `⊢ $A` and
`empty ⊢ $A`: `"theorem-to-empty-sequent"`, `"empty-sequent-to-theorem"`) — at the cost of one
explicit conversion step per use, since it isn't wired into `let`'s automatic block-closing. See
`dev/todo.md` #36 for a planned worked example.

**What it would take to add the automatic dispatch.** An engineering change, not a foundational
one: `role_symbol`/`let`/`pick` would need to look up the constant's sort and dispatch on it
instead of assuming one global holder. Real and scoped, much smaller than anything in §2 — but pure
ergonomics: it would shorten some two-sorted theories' notation, not unlock any new theorem, since
the sort-conditioned `∀` above already has the same expressive power.

## 4. Summary

| Want | Blocked? | Why | What works instead |
|---|---|---|---|
| Structural induction over a closed, first-order inductively-presented sort | No | `%A`-schema axioms are fully general, same device as `natural.kurt` (§1) | Write the axiom |
| General preservation / Church–Rosser for `lambda.kurt`, stated over the de Bruijn encoding | No: preservation done (2026-10-20), Church–Rosser done (2026-10-24) | `term` also contains `λ` (§2.2), so the proofs define their own de Bruijn calculus (sorts `tm`, `ty`, `cx`); induction + weakening + substitution lemma, all first-order (§5.5); parallel reduction, complete development, the closures as inductive relations (§5.7) | proofs/classics/lambda-preservation.kurt, proofs/classics/lambda-church-rosser.kurt |
| Structural induction over a sort with a Kurt binder (HOAS `lam x M`) | **Yes** (§2.5) | The `lam` case of the axiom covers only bodies that don't depend on `x`; with no-confusion axioms it proves `false` | The de Bruijn presentation |
| A proof about the generic named β-step `sub x N M` | **Yes** (§2.5) | `sub` is refused in proof lines; typing inversion for named `λ` is a disjunction over body shapes, no formula | The de Bruijn presentation |
| A theorem quantified over real functions as values (`∀ f ∈ ℝ → ℝ`, continuity of `f`) | **Yes** (§5.3) | A mapping applied, `f y`, has the sort `set` of the mapping, never `real`; analysis needs `real` (`cont y x (f y)` is a type error) | A schema over a function symbol (`var f`), applied to any function symbol |
| The number of elements of a finite set (Lagrange, pigeonhole) | No: finite.kurt (2026-10-24) | `hassize(A, n)` (a bijection from `below(n)` = {0, ..., n - 1} onto A) is a `def`, its lemmas theorems; `card` can't be a `def` (no description operator), the relation says the same | src/kurt/theories/finite.kurt, proofs/classics/lagrange.kurt |
| Stating the general preservation substitution lemma (one `sub`) | No | Single-`sub` facts parse and type-check fine; the restriction is on *nested* `sub` only (§2.3, hypothesis 2) | State it directly, prove by induction, one `sub` per step |
| A general fact that composes two substitutions ("substitutions commute") | **Yes**, but doesn't matter here | `sub` can't be nested in one expression, and can't appear outside `use`/`def` at all (§2.3, hypothesis 2) | Not needed for preservation, and not needed for confluence via the standard parallel-reduction route either (todo #37) |
| A fully general named hypothetical-premise rule (`Γ,x:A⊢M:B ⟹ Γ⊢λx.M:A→B`) for Kurt's own binder | **Yes** | Accepted when declared, but unusable: `block_always(v_p)` keeps the binder's bound-name permanently unassignable for the rest of the rule's matching, by design (it's what makes `forall-elim` sound). A candidate fix was attempted and crashed an existing adversarial regression test (`search-bugs-the-kernel-caught.kurt`), and turned out to need a second, separate change (`dependent_vars`/`may_capture` doesn't cover this pattern either) even before that — reverted (§2.3 hypothesis 3, §2.4) | State the general theorems over the de Bruijn encoding; keep named `λ` as sugar for closed, individually-checked examples |
| Second-order logic: quantifying over sets as well as individuals | No | `sort` + `set.kurt`'s `℘` + a domain-conditioned `∀`/`let` is already fully sound and general (§3) | `let X ∈ ℘(Obj) (...)` |
| Two `sub`s in one formula ("substitutions commute") | **Not wanted** (decided 2026-10-20, doc/kurt-ref.md §11.1: the matching would become higher-order unification; nothing known needs it) | |
| The named hypothetical-premise rule for Kurt's own binder | **Not wanted** (decided 2026-10-20, doc/kurt-ref.md §11.1: the bound name would leave its binder; the de Bruijn presentation has the general rule) | |
| A *second, visually distinct* quantifier glyph that still gets `let`'s automatic generalization | **Not wanted** (decided 2026-10-20, dev/todo-sorts.md decision 14: the sort of a binder distinguishes the ranges) | `let`/`pick` dispatch to one global role-holder, not by sort; a hand-written intro axiom as a substitute would be unsound without proof-state-aware freshness tracking (§3) | Use the one real `∀`/`let` with a domain condition; add the second glyph as notation bridged to `∀` by a proven equivalence if wanted |

The real limit (§2.3's hypothesis 3) and the near-misses (§1's prerequisite, §2.3's hypothesis 2,
§3) are different in kind. The real limit is a specific, reproducible gap in the matching engine's
variable-renaming, not a missing order of logic — the same renaming machinery already correctly
handles the mirror-image case (`forall-elim`), after a real, documented soundness bug of its own. A
first attempt at extending it (§2.4) crashed an existing adversarial regression test and turned out
to need a second, independent change on top, even before the crash — concrete evidence that this
is not a small, scoped engineering fix, and that a dedicated device (`∇`, contextual types) is the
likelier real route, though not a certainty. §3's gap is an engineering choice already worked
around by existing machinery (conditioned quantification) — not a soundness or expressiveness
question at all, and the existing single-quantifier-with-conditions approach is both sound and
already in daily use (`natural.kurt`, `set.kurt`).

## 5. Classic theorems, attempted (todo 44, 2026-10-20)

Each theorem below was attempted as a Kurt proof in `proofs/classics/` (each file checks, so each is
a test). The question was where Kurt, as it is -- no change to `kurt.py` or to the theories' rules --
stops. Every `use` of these files is a hypothesis about new constants ("let G be a group") or a
standard definition, and says so in a comment.

| Theorem | Result | File |
|---|---|---|
| Cantor: no mapping from A onto Pow(A) | works, general in A and f | cantor.kurt |
| Euclid: infinitely many primes (above every n a prime) | works, no axiom | infinitely-many-primes.kurt |
| Intermediate value theorem | works, a schema in the function (`var f`) and `$a`, `$b`, applied to a function symbol | intermediate-value-theorem.kurt |
| Lagrange | works: the cosets partition G and each is in bijection with H; |G| = [G : H] · |H| and |H| divides |G| by induction on unions of cosets, with finite.kurt (§5.4) | lagrange.kurt |
| Preservation (subject reduction), simply typed λ, call-by-value | works, for a de Bruijn calculus defined in the file (§5.5) | lambda-preservation.kurt |
| Knaster-Tarski for a power set (extra) | works | knaster-tarski.kurt |
| Church-Rosser, untyped λ, full β-reduction | works, for a de Bruijn calculus defined in the file: parallel reduction, Takahashi's complete development, the closures as inductive relations (§5.7) | lambda-church-rosser.kurt |

The proofs need no new feature for what they prove; what they found is listed by theorem. Four of the
limits of the search found here were fixed afterwards (todo 52, 2026-10-23), marked below. Through
`kurt --lean` and Lean with Mathlib (SLURM job 115579, dev/lab-notes.md), cantor.kurt and
knaster-tarski.kurt check completely; the exports of the other four fail in Lean for gaps of the
export (a `def` over a set-builder not unfolded, an operator argument exported as an object, a sort
of a `let` constant lost), listed in the lab notes.

### 5.1 Cantor

The diagonal argument goes through as on paper (`diag(A, f) = {x ∈ A | ¬(x ∈ f x)}`). One trap on
the way: set.kurt declares `set $f, $g` for its own rules, and a loading file can't declare `set $f`
("it would change the meaning of `$f`, which comes with a theory"), although its `$f` has no sort --
the declaration doesn't cross `load`, the refusal does. A `show` about `$f a` then has an unsorted
`$f`, a line of its proof (`a ∈ $f a`) gives the block's `$f` the sort `set`, and the closed block
no longer matches the claim: "can not derive" at the `show`, without a word about sorts. The file
declares its own `set $h`.

### 5.2 Infinitely many primes

Through without a limit: `prime` is a `def`, the prime divisor of n! + 1 comes from the
well-ordering of `Nat` (the least divisor ≥ 2), n! from numbers.kurt's `!`. Idioms needed: under
`default real`, `S ⊂ Nat` for a set built with separation needs a block constant of the sort `any`
(`any c` before `let c`), since "subset" is about all objects; and a bound variable may not reuse a
name that an enclosing `let`/`pick` made a constant (`∃ q`, not `∃ p`, inside `pick p`).

### 5.3 The intermediate value theorem

Through: c = sup {x ∈ [a, b] | f(x) ≤ 0} by analysis.kurt's "sup-upper" and "sup-least" (the
completeness of the numbers), continuity by "cont-def", and the two cases f(c) < 0 and f(c) > 0 by
ε = |f(c)|, δ/2. The limits found:

- **A real function as a value can't enter analysis.** For a mapping `g ∈ A → B` (set.kurt), `g y`
  has the sort `set` -- the sort of a value comes from the syntax, never from `g ∈ A → Real` --, and
  `cont y x (g y)` is a type error ("`g y` must have sort `real`"). So "for every continuous `f : [a, b]
  → ℝ`" can't be a quantifier; the theorem is a schema over a function symbol (`var f`, an operator
  variable as in group.kurt), and it applies to any function symbol `g` in one step. Since an operator
  is no object (doc/kurt-ref.md §5.3), the function can't be quantified either way.
- **Bug, fixed 2026-10-20** (`proofs/soundness/inline-condition-binds-the-written-variable.kurt`,
  doc/kurt-soundness.md §8.49): the bound variable of a condition with an `inline` operator. `∀ x > y (P x)` bound `y`,
  not `x`, and makes `x` a constant: the condition is read as `y < x` (the `inline` of `>`) before the
  bound variable is chosen as the first new symbol, against doc/kurt-ref.md §4.4 ("decided when it
  reads the line, before anything is reordered"). The same for `>=` and `⊃`, and for `$` variables:
  `use ∀ (x >= $a) (P x)` is `∀ $a ($a <= x ⇒ P x)` for a constant `x`. Nothing warns. (The proof writes
  `x <= $b ∧ $a <= x` instead.)
- `let w with $a <= w ∧ ...` was refused when `$a` is fixed by an enclosing `assume` ("expected exactly
  one new symbol or existing, got ['$a', 'w', '$b']"), though the fixed `$a` is no new symbol there.
  **Fixed 2026-10-23** (todo 52, proofs/debug/let-condition-with-a-fixed-variable.kurt): a variable fixed
  by an enclosing block is no candidate, as for a binder; the proof now writes `let w with ...`.

### 5.4 Lagrange

The cosets `coset(a) = {x ∈ G | ∃ h ∈ H (x = a ∘ h)}` are equal or disjoint and cover G, and `h ↦ a
∘ h` is a bijection from H onto aH -- a mapping built as a set of pairs with separation, proved to be
in `H → coset(a)` from "function-space", injective and surjective. The counting (2026-10-24) uses
finite.kurt: `hassize(A, n)` ("A has n elements", a bijection from `below(n)` = {0, ..., n - 1} onto A)
with its lemmas, all proved there (adding and removing an element, uniqueness of n, a bijection keeps
it, disjoint unions add up, subsets are no larger). `card` can't be a `def` (Kurt has no description
operator "the n with ..."), so the index [G : H] is "the set `cosets(G)` of the cosets has l
elements". Lagrange's theorem, "lagrange": `hassize(G, N) ∧ hassize(H, K) ⇒ ∃ l (hassize(cosets(G),
l) ∧ N = l * K)`, by induction on j: every union of cosets T with i <= j elements has i = l · K, with
l the number of its cosets (take one coset out: i - K elements left, one coset fewer). Two traps: a
function whose value is a mapping, `shift(a) h`, is read as `shift a h` (one curried call) unless
`arity shift 1` is declared (doc/kurt-ref.md §3.1); and since a fact gives no sort, an element `x ∈
below(n)` is any object for the checker -- finite.kurt's one axiom, "nat-number" (`x ∈ Nat ⇒ ∃ k (k =
x)`, a theorem in the Lean model), gives the number equal to it.

### 5.5 Preservation for the simply typed λ-calculus

lambda.kurt's `term` contains the named `λ` (§2.2), and a theorem about named terms is out of reach
(§2.5), so the file defines its own de Bruijn calculus: terms `ix n`, `lam A M`, `app M N`, `unit`
with their structural induction, contexts as functions from indices to types (`get Γ n`, `ins c A Γ`
inserts A at c), typing and call-by-value steps by recursion on the term, `shift` and `subst`
by their recursive equations. Weakening, the substitution lemma and preservation are each proved by
induction on the term; the index arithmetic uses numbers.kurt (indices are numbers). The limits
found are of the search, each with a workaround:

- **Induction over a universally quantified property.** A goal `∀ Q ∀ Γ ∀ T (...)` was read with all
  its outer `∀`s stripped, so an induction rule concluding `∀ $s (sub $t $s %P)` got `%P` without the
  inner `∀ Γ ∀ T` -- the induction hypothesis was then about one fixed Γ, too weak (minimal: a tree
  induction for `∀ s ∀ y (R s y)` asked for `∀ l ∀ r ((R l y) ∧ (R r y) ⇒ R (node l r) y)`). The
  workaround was to name the property, `def weakens(M) ⇔ ∀ Γ ...`. **Fixed 2026-10-23** (todo 52,
  proofs/debug/induction-over-a-forall-property.kurt): when the stripped goal fails, the whole goal is
  matched against the conclusion with its `∀`s too; the file proves `∀ Q ∀ Γ ∀ T ...` directly.
- **The form of an induction rule's conclusion.** `... ⇒ ∀ $t %P` was never applied by the search
  (its outer `∀` stripped, leaving a bare `%P`, which lost the link to `$t`); `... ⇒ ∀ $s (sub $t $s %P)`
  was. **Fixed 2026-10-23** by the same change: the whole goal `∀ s P(s)` matches `∀ $t %P` with
  `%P = P($t)` (the same test file).
- **A lemma with nested `∀`s can't be unfolded inside a block that fixes its variables.** Inside
  `let Γ, T, c, D`, the line `∀ Γ ∀ T ... ` is refused ("first arg of binding operator must not be
  constant"), so the induction hypothesis is unfolded before the `let` (in the `assume`), and the
  lemmas' instances are lemmas of their own at the top ("weakening-0", "substitution-0").
- Conditional rewriting in a chain (doc/kurt-ref.md §6.1): in the lemma "ins-ins", `get (ins 0 B
  (ins c A Γ)) n = get (ins c A Γ) n` continued by `= get Γ n` (rule "get-ins-below", its condition
  `n < c` a fact) was not found, while the same chain in a small file was; the instance as a line of its
  own first worked. The difference: `A`, `B`, `Γ` are free variables there, and each line has its own
  names for them, so the line before differed from the next one everywhere, not only at the place
  rewritten. **Fixed 2026-10-23** (todo 52, proofs/debug/conditional-rewrite-with-free-variables.kurt):
  as a last try, the line before is compared under the names of the next one; four instance lines are
  gone from the file.
- The failure explanations list, for a rule whose conclusion didn't match, "`$a` needs sort `real`,
  but `get Γ n` has no declared sort", for a term whose sort is declared (`ty get 0`): the
  diagnostic of todo 38 misreports the sort of an application.

### 5.6 Knaster-Tarski

Through, for a monotone mapping `f ∈ Pow(A) → Pow(A)`: L = {x ∈ A | ∀ S ∈ Pow(A) (f S ⊂ S ⇒ x ∈ S)} is
a fixed point and below every fixed point. (Schröder-Bernstein would follow from it, with images,
complements and a mapping defined by cases -- long, not attempted.)

### 5.7 Church-Rosser for the untyped λ-calculus

proofs/classics/lambda-church-rosser.kurt (2026-10-24): the calculus of §5.5 without types and
`unit`, full β-reduction `->` and its closure `->*`; Tait and Martin-Löf's parallel reduction `>>`
with Takahashi's complete development `dev` ("par-dev", then "par-diamond"), the strip lemma,
confluence of `>>*`, `>>*` = `->*`, and "church-rosser". The de Bruijn lemmas (shift/shift,
shift/subst at both sides, subst/shift, subst/subst) and the substitution lemma for `>>` are each
an induction on the term over a `∀` property, as in §5.5. No language limit; what was found:

- **The indices must be natural numbers.** With any number as an index (as in §5.5), "shift-subst"
  is false: an index strictly between d and d + 1 is lowered below c by `subst` but not by `shift`
  (c = d = 0, n = 1/2). The rules for a variable take `n ∈ Nat`, `c ∈ Nat` as hypotheses, the term
  induction ranges over `ix n` with `n ∈ Nat`, and natural.kurt's "nat-discrete" gives d + 1 <= n
  from d < n ("nat-above").
- §2.3's follow-up said the parallel-reduction route needs no "substitutions commute" lemma. For
  Kurt's own `sub` that holds; with de Bruijn's `subst` the β-in-β case of "par-subst" does need it
  ("subst-subst": `subst c N (subst 0 R P) = subst 0 (subst c N R) (subst (c + 1) (shift 0 N) P)`),
  but as an equation between ordinary terms, proved by induction -- no nested `sub`.
- **A two-place induction principle can't be written** (nested `sub` is refused, §2.3): the closures
  `>>*`, `->*` are inductive relations whose rule induction is stated for a fixed end P (`sub M P %A`
  and back along a step, `⇒ ∀ Q (Q >>* P ⇒ sub M Q %A)`). That is enough: the strip lemma, confluence
  and transitivity all induct on the start with the end fixed.
- Limits of the search, each with an extra line: a chain step that rewrites two places at once
  (`= app (f F) (f P)` from `app F P` with two equations) is not found -- one place per step; an
  `∃ x ∃ y (...)` is introduced one quantifier at a time; a fact under two `∃` (`F = lam B` in
  `∃ B ∃ B' ∃ Q' (F = lam B ∧ ...)`) is reached by `pick`ing all three, not from the first `pick`.
- Speed: 53 s for the file without `.kurtc` (lambda-preservation.kurt: 14 s); 40% of it in
  `add_assumption_parts`, the parts of the `assume (∀ ... F ...) ∧ (∀ ... P ...)` of the application
  cases (todo 50).
