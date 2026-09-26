# todo-claude.md

A pass over `todo.md` plus a read-through of `src/kurt/kurt.py`, sorted by
what's actually actionable. For each item I checked the current behaviour
(usually by running a small `.kurt` snippet through the interpreter) rather
than just trusting the one-line description in `todo.md`. Items are grouped
by how ready-to-pick-up they are, not by which section of `todo.md` they came
from. The original `todo.md` wording is quoted or paraphrased; my notes
follow.

No code was changed while producing this file.

## Theory completeness pass (in progress, working one at a time)

Kurt-web now vendors and lets users freely browse/`load` all 11 shipped
theories (`src/kurt/theories/*.kurt`), not just 3 — which turned "some
theories are thin or empty stubs" from a hidden internal detail into a
user-facing gap. Assessed each file's actual state (content depth + how
much, if any, real proof anywhere in the repo exercises it — not just
"does it load without error"); the goal now is to work through the
list, one theory at a time: fill in real gaps, then write permanent
test proofs under `proofs/` that actually exercise the new (and
existing, previously-untested) content, not just smoke-test that it
loads. Order below is roughly easiest/most-contained first.

Status as assessed:
- ~~**`arith.kurt`**~~ — **done.** Added the two real content gaps: `pow-zero`
  (`$a ≠ 0 ⇒ $a^0=1`, guarded to dodge 0^0), `pow-add`, `pow-mul` (real
  exponent laws, previously commented out entirely), and `factorial-step`
  (`$n>0 ⇒ $n!=$n*($n-1)!` — previously only the base case existed, so no
  factorial past `0!` was derivable at all). Wrote 4 permanent test proofs
  under `proofs/arithmetic/` exercising all of this plus the previously-
  completely-untested order theory (`order-transitivity-chain.kurt` chains
  two `lt-trans` applications; `order-antisymmetry.kurt` exercises
  `le-ge-antisym`; `exponent-laws.kurt` and `factorial-recursion.kurt` cover
  the new axioms). Also fixed two unrelated cosmetic issues found in
  `prop.kurt` along the way: two duplicate labels (`"iff-elim"` used twice,
  `"not-intro"` used twice — renamed to `"iff-elim-forward"`/
  `"iff-elim-backward"` and `"not-not-intro"`) and a stray leftover `trail`
  debug statement right before the end-of-file marker. Found (but
  deliberately did not fix, see `doc/kurt-soundness.md` §6) a real matching-
  engine limitation while writing `factorial-recursion.kurt`: chaining two
  `equal-elim` substitutions where the substituted value reuses the same
  `flat` operator as its context (`*`, here) doesn't re-flatten correctly —
  a completeness gap in `derive_expr`, not a soundness one, and not specific
  to `arith.kurt` — flagged for separate dedicated investigation.
- ~~**`modal.kurt`**~~ — **done, and found a real bug in the process, bigger
  than the "needs a test proof" framing suggested.** Every axiom
  (`diamond-def`, `box-def`, `diamond-distrib-or`, `box-distrib-and`, `K`,
  `T`) was written with plain symbols (`p`, `q`, `A`, `B`) instead of
  `%`-prefixed schema variables, unlike every other theory in the repo —
  silently pinning every axiom to those two exact hardcoded propositions.
  Confirmed directly before fixing: `use □(X ⇒ Y)` + `use □X` could never
  derive `□Y`, only the literal `□(p ⇒ q)` + `□p` could ever derive `□q` —
  `K` (and the rest) were unusable for anything except the two symbols
  the file itself happened to declare. Fixed by rewriting all six axioms
  with `%p`/`%q`, and removed the now-unnecessary `bool A, B, p, q`
  declaration (only `b`/`d`, the box/diamond operator symbols themselves,
  are still real constants). 3 new permanent test proofs under
  `proofs/modal-logic/`, deliberately using `X`/`Y` rather than the file's
  own `p`/`q` example symbols specifically so they'd have caught this bug
  (confirmed: reverting the fix breaks all three).
- ~~**`natural.kurt`**~~ — **done.** Content itself was already correct
  (confirmed while fixing the crash bug above); what it needed was the
  permanent real induction proof, now added:
  `proofs/natural-numbers/induction.kurt` (an uninterpreted predicate `P`,
  same style as `proofs/natural-deduction/forall-elim.kurt` etc. — there's
  no richer concrete property of numbers to induct over yet, since `+` has
  no defining axioms here, see the file's own new header). Also added a
  proper documentation header to the file itself (see the new "document
  theories well" item below).
- ~~**`set.kurt`**~~ — **done.** Filled the `:`/`→` gap: mappings are
  modelled as opaque, applicable set objects (reusing kurt's existing
  general space-application, `$f $a` — no new syntax needed), `A → B` is
  *defined* as the set of all A→B mappings via the same comprehension
  machinery as `∩`/`∪`/`Pow` ("function-space"/"function-space-def"), `:`
  is a plain alias of `in` (so `f : A → B` parses as `f ∈ (A → B)`, exactly
  like `∈` is already an alias of `in`), and function extensionality is
  added as a genuine new axiom (not derivable here, unlike `∩`/`∪`'s
  properties — see the file's own comment on why). Deliberately did *not*
  build full ZF-style pairs/products/relations — a much bigger, separate
  undertaking than this gap warranted. 3 new tests under
  `proofs/set-theory/`. Caught my own mistake while writing the negative
  test: an earlier "confirmed function-extensionality works" check had
  actually been silently exploiting the `forall-elim` soundness bug (§0)
  rather than testing the new axiom at all — re-verified properly using
  the "combine the whole antecedent into one conjunction" pattern
  `impl_elim`'s single-hop matching needs (same as `induction`'s
  base-and-step).
- ~~**Severe soundness bug: `forall-elim` could prove any two things
  equal**~~ — **found (while testing the above) and fixed.** `load logic,
  equality` alone let `f = g` derive for two unrelated constants, no
  premise at all — nothing to do with `set.kurt`. See
  `doc/kurt-soundness.md` §0 for the full mechanism and fix; this was the
  single most severe finding of the whole session. Also fixed a genuine
  proof (`proofs/mafi1/001-two-equal-sets.kurt`) that turned out to have
  been passing only by accidentally relying on the same bug.
- ~~**`induction.kurt`**~~ — **removed**, per explicit maintainer decision:
  `natural.kurt` already has the one induction principle actually wanted
  (Peano-style, over `Nat`) — a separate general/transfinite/well-founded
  induction theory is deliberately out of scope for now, so the empty stub
  was deleted rather than filled in. Removed its `theory` table row in
  `doc/kurt-doc.md`, its mention in `CLAUDE.md`'s file list, and the stale
  `induction.kurt`+`lambda-calculus.kurt` pairing in `suggestions-claude.md`
  (that suggestion's example now just points at `lambda-calculus.kurt`).
- ~~**`lambda-calculus.kurt`**~~ — **done, with real, load-bearing scope
  limits found and documented, not just "less complete than I'd like."**
  Abstraction is `λ $x %B` — a `bindop` (`arity lambda 2`), exactly like
  `forall`/`exists`; application needs no new syntax at all, since `(λ $x
  %B) $a` is already just ordinary space-juxtaposition (`set.kurt`'s `$f
  $a` idiom). Beta-reduction reuses kurt's own built-in `sub` operator
  directly (`use (λ $x %B) $a = sub $x $a %B`) rather than defining a new
  substitution function from scratch — and alpha-equivalence is free too,
  via kurt's existing bound-variable-aware matching.
  The real discovery, from actually trying to get beta-reduction to
  *derive*, not just parse: `sub`'s schema-decomposition matching (the
  mechanism that lets a concrete goal be matched against `sub $x $a %A` by
  figuring out what `%A` must have been) only fires when the thing being
  substituted into is **boolean-typed** (`match_against_sub` requires
  `kb.is_bool` on that schema var) — confirmed by testing a non-boolean
  `$B` directly (fails to derive) vs a boolean `%B` (works). This makes
  the file a genuine but *restricted* lambda calculus: bodies must be
  boolean (a predicate about the bound variable, e.g. `P($x)`), which
  rules out the fully general, arbitrary-valued untyped lambda calculus.
  Two further gaps found the same way, both real matching-engine
  limitations rather than anything specific to lambda calculus: (1) a
  body that's *exactly* the bound variable and nothing else (the identity
  function) doesn't beta-reduce — the decomposition mechanism doesn't
  find that degenerate a "hole"; (2) currying (a lambda whose body is
  itself another lambda) doesn't beta-reduce either, even with the inner
  lambda's own body boolean — the decomposition mechanism can't find a
  "hole" that itself contains a binder, so every lambda here ends up
  single-argument, no curried multi-argument application. Deliberately
  did not add eta-conversion (`λx.(f x) = f`, provided `x` doesn't occur
  free in `f`) — kurt's axiom syntax has no way to state that side
  condition, and omitting it would be unsound (nothing would stop `f`
  from being instantiated to something that does mention `x`).
  All three gaps are completeness limitations, not soundness ones — kurt
  correctly refuses to derive what it can't find a decomposition for, it
  never derives anything wrong.
  Regression tests: `proofs/lambda-calculus/beta-reduction.kurt` (four
  worked examples: single predicate, argument that's itself an
  application, a compound `and` body, a body under `not`) and
  `known-gaps.kurt` (the identity and currying cases, each wrapped in
  `expect "ProofError"` to confirm the limitation is real and stays
  documented). Theory table entry updated in `doc/kurt-doc.md` §8.2.
- **`prop.kurt`**/**`logic.kurt`**/**`equality.kurt`**/**`minimal.kurt`** —
  solid, heavily exercised (34/28/18 files respectively; `minimal.kurt` is
  intentionally unloadable reference documentation, not meant to carry
  proof weight). Only issues found were cosmetic and already fixed: two
  duplicate labels in `prop.kurt` (`"iff-elim"` used twice, `"not-intro"`
  used twice — labels don't need to be unique for correctness, matching
  never keys off them, but a duplicate makes the printed `by "label"` reason
  ambiguous) and a stray leftover `trail` debug statement right before the
  end-of-file marker.
- **`latex.kurt`** — not a proof theory (a symbol→LaTeX-macro table for
  `-l`/`format latex`), so "complete" means something different here: it
  only covers propositional-logic symbols/keywords, missing everything from
  `arith`/`set`/`modal`/`natural` (`+`, `∈`, `⊂`, box/diamond, `Nat`, ...)
  and several newer keywords (`local`, `expect`, `sandbox`). Also has one
  dead entry, `latex "equiv" "\Leftrightarrow"`, mapping a symbol name
  that doesn't exist anywhere in kurt's actual grammar. Lower priority than
  the proof theories above since it only affects LaTeX rendering, never
  proving/checking.

- ~~**Document every theory's scope inside the `.kurt` file itself**~~ —
  **done for the 8 theories with real content.** Every shipped theory used
  to open with just a one-line title comment (`; arithmetic`, `; modal
  logic`, ...) and nothing else — no stated scope, no "what this doesn't
  cover," no pointer to a real example proof. Added a proper header (scope,
  known gaps, pointer to a real proof under `proofs/`) to `natural.kurt`,
  `arith.kurt`, `modal.kurt`, `prop.kurt`, `logic.kurt`, `equality.kurt`,
  `set.kurt`, `latex.kurt`. `minimal.kurt` already had one (rewritten
  earlier this session). Left `lambda-calculus.kurt` (still empty) for
  whenever its real content gets written — no point documenting the scope
  of a file that's still empty. (`induction.kurt` itself was later removed
  entirely, see above.)

## Documentation review pass

- ~~**Re-check `doc/kurt-doc.md`, `tutorial/*.kurt`, and other docs for
  staleness**~~ — **done.** Given how much changed this session (`thus`,
  `save`, `commit`, `nonassoc`, `f()`, chain transitivity), swept for
  claims that were no longer true. Found and fixed: §11 "Known gaps" still
  said `f()` doesn't parse (fixed this session); §8.2's theory table didn't
  mention set.kurt's mapping/function-space additions; `tutorial/plan.md`
  said `thus` was "a future, not-yet-implemented shortcut" (also fixed
  this session) and its "File and shell are now handled identically"
  section only described `qed`/`break` as the position-independent
  block-closers, missing `thus`/`commit` entirely. Also added a one-line
  "Known gaps" mention that `inspect` is listed by `help` but not
  implemented (raises `NotImplementedError`), since nothing said so
  anywhere before. `README.md` and `doc/kurt-cookbook.md` (still
  deliberately just a stub) checked and found still accurate/unchanged.
  `doc/dev-notes.md` deliberately left untouched — it's a chronological
  design diary (see this file's own instructions), not a reference, so an
  old entry describing `thus`'s original, more ambitious design (as the
  general block-closer for every block type, not just `proof`) is
  correctly a historical record, not something to "fix" to match what
  actually got built.
  Wrote four missing tutorial lessons for keywords that had none:
  `tutorial/09a-thus.kurt`, `11-save.kurt`, `14a-commit.kurt`,
  `40-nonassoc.kurt` (numbered with a letter suffix to slot in next to
  their closest relative without renumbering every later lesson) — the
  plan's own stated rule is "one lesson per keyword," and these four had
  none. Updated `tutorial/plan.md`'s lesson list and prose to match.

- ~~**New finding: a blank line inside a nested block could silently close
  it**~~ — **done, fixed.** Found while writing `tutorial/47-worked-proof.kurt`.
  A blank line's own leading-space count is always 0, and the indentation
  tracker read that literally as "dedent all the way back to column 0" --
  incorrectly closing *every* currently open block instead of being
  ignored, regardless of how deeply nested the blank line actually was.
  Two distinct symptoms depending on exactly where the blank line landed:
  a confusing `ParseError: expected increased indentation` (if it came
  right after a block-opening keyword still waiting for its first indented
  line), or worse, *silently* closing blocks early and skipping real
  content that was never parsed at all (if it came after an ordinary
  statement mid-block -- the exact shape that surfaced this: a blank line
  right after an `expect` block that had just confirmed an error, which
  pops its own level, leaving the parent block's still-nonzero
  indentation in force for the next line). Fixed in `read_eval_loop`: a
  blank line, when not already mid-statement (an unclosed bracket
  spanning a blank line is still part of that statement), is now skipped
  outright before it ever reaches the indentation logic. Verified via
  `git stash` that the minimal case reproduces pre-fix and is fixed after;
  full test suite unaffected (95/95), confirming the fix only makes more
  input accepted, nothing that previously worked stopped working.
  Regression test: `proofs/debug/blank-line-inside-block.kurt`. Documented
  in `doc/kurt-doc.md` §2.1.

## Testing-infrastructure follow-up

- ~~**Revisit the `;;; ` marker convention more broadly**~~ — **done.**
  `file_last_line` now defaults to expecting clean success (no exception)
  for *any* file with no `;;; ` marker at all, regardless of whether it
  uses `expect` — removing `uses_expect` entirely, since the two cases
  (uses `expect`, or is just an ordinary successful proof) always wanted
  the exact same default. A marker is now needed only for the genuinely
  special cases: a file whose point is a *specific* failure that happens
  while a block *closes* (`expect` can't wrap that — it only observes an
  error from an ordinary statement inside its own body) or specific
  non-error output text.
  Applied a bulk cleanup across every `proofs/*.kurt` and
  `src/kurt/theories/*.kurt` file: removed the now-redundant `;;;
  Proof checked.` marker line (109 files) wherever it was the file's
  literal last line. Left every genuinely specific marker
  (`;;; ProofError: ...`, `;;; EvalError: ...`, etc.) untouched — those
  still serve a real purpose the new default can't provide.
  Along the way, the bulk cleanup surfaced three unrelated, genuine
  problems that a marker had been silently masking: two test files I'd
  just written this session (`proofs/debug/pick-error-messages.kurt`,
  `proofs/soundness/iff-third-attempt-still-works-legitimately.kurt`) left
  a `pick`/`let` block open at end-of-file — `load_file` raises
  `EvalError: ... not all blocks closed` for that, but my own earlier
  `tail`-only spot-checks of their output never happened to show the error
  line (stdout/stderr interleaving under `2>&1` put it above the visible
  window), so I never noticed it hadn't actually been passing; fixed by
  adding a closing dedent to each. Third:
  `proofs/debug/todo.kurt` had two *explanatory comment* lines that
  happened to also start with `;;; ` (not intended as markers at all,
  just written with the same prefix), which the new "last line only"
  check would have latched onto once the real marker after them was
  removed — reworded them to plain `;` comments. Also found and fixed two
  cosmetic-only pre-existing oddities the bulk pass's "must be the exact
  last line" check surfaced: `proofs/natural-deduction/or-commutative.kurt`
  had a stray `;;; Proof checked.` sitting in the *middle* of the file
  (after its first of two `show`/`proof`/`qed` blocks) that the harness
  never actually checked even before this change (`file_last_line` always
  only looked at the true last line) — pure dead noise, removed; and
  `proofs/mafi1/001-two-equal-sets.kurt` opened with `;;; two-equal sets`
  as a title-style comment, not a marker — reworded to a plain `;` comment
  to avoid it ever being mistaken for one.
  Updated `tests/how-to-write-test-proofs.md` and `CLAUDE.md`'s own
  description of the convention to match.

## Already done / stale (recommend deleting from `todo.md`)

- **"get group.kurt working with constants and with `var x, y, z`"** —
  `proofs/linear-algebra/group.kurt` already declares `var x, y, z` and is
  part of the auto-discovered test suite; it passes today (`python3 -m
  unittest` — 49/49). Nothing to do.
- **"allow boolean expressions for the bound variable for some binding
  operators"** — already implemented: `type_check_expression`'s `bindop`
  case (around line 2900) and `unpack_condition` (line 2150) both handle
  `forall x>0 F(x)`-style conditions. Confirmed working (`tutorial/19-let.kurt`
  relies on the simple form; the doc's own example `forall x>0 F(x)` also
  parses).
- **"what is the difference between `arity f 1` and `prefix f 1`?"** —
  answered already, in `doc/dev-notes.md`'s 2025-04-17 section
  ("difference between prefix and function") — not `doc/kurt-doc.md`, which
  doesn't have this heading (dev-notes.md is the design-decision diary, per
  CLAUDE.md; this belongs there, not in the reference doc). Just needs the
  todo removed.
- **"add syntactic sugar for case distinctions"** — `case` already exists as
  a full keyword (identical to `assume`, feeding "or-elim"); see
  `tutorial/21-case.kurt`. Todo is stale.
- **"write the tutorial" / "write documentation/tutorial for the language"**
  — done in `tutorial/*.kurt` (45 lesson files) + `tutorial/plan.md`. Worth a
  follow-up: `doc/kurt-tutorial.md` still says "Not yet!" — point it at
  `tutorial/` instead of leaving a dead stub.
- **"add column information for the exceptions, use `expr_column`"** —
  `expr_column()` (line 2861) already exists and is already used at most
  `raise KurtException(..., column=...)` call sites I checked
  (`type_check_expression`, `eval_use`, etc). What's left is an audit for the
  remaining call sites that pass no `column`/pass `None` — a grep-and-fix
  pass, not new infrastructure. Low effort.
- **"use the `Token.column` information"** — same as above, largely already
  wired up; remaining work is the same audit.

## Quick, low-risk fixes (do these first)

- ~~**Exit code is always 0**~~ — **fixed.** `main()` now tracks whether the
  non-interactive file check raised a `KurtException` (a new `had_error`
  flag) and exits `1` if so, `0` otherwise — a genuinely failed/crashed
  check (`ProofError`, `SyntaxError`, ...) is now visible to a script (CI, an
  autograder) from the exit code alone, not just by scraping stderr text.
  Deliberately left as a judgment call, unchanged: leftover `todo`s in an
  "almost checked" file still exit `0`, since a `todo` is a deliberate,
  self-reported placeholder, not a failure; and errors raised *during* an
  interactive REPL session don't affect the exit code either, matching how a
  Python REPL exits `0` regardless of exceptions raised while typing at it.
  Regression tests in `tests/test_cli_exit_code.py` (subprocess-based, since
  this is CLI/process behaviour, not something the in-process proof-file
  harness can observe).
- ~~**"repair messages for 'pick', 'fix', 'assume'"**~~ — **fixed.**
  `eval_keyword_expression`'s `let` branch still raised `EvalError: \`fix\`
  takes new constants...` even though the keyword was renamed to `let`
  everywhere else. One-line string fix; regression test
  `proofs/soundness/let-empty-error-message-mentions-let.kurt` (checks the
  message text, not just the error kind, since both old and new wording
  are equally rejected — only the wording was wrong).
- ~~**`format latex` is unreachable from a `.kurt` file**~~ — **fixed.** Root
  cause: `latex` is itself a reserved keyword (also used for the separate
  `latex <key> <value>` command), so `parse_tokenstream`'s generic
  `check_no_keyword` check rejected it as an argument
  (`SyntaxError: keywords not allowed inside expressions`) before
  `eval_global_format` ever got a chance to validate it against
  `format_options`. Fixed by skipping that check specifically for
  `format`'s own arguments — safe, since they're immediately validated
  against the small fixed `format_options` list right afterwards anyway, so
  there's no way to smuggle a real keyword through. Also fixed an unrelated
  cosmetic bug turned up alongside it: the "possible is:" error listing ran
  option names together with no space (`formatnormal`) due to a
  missing-space typo in the join separator. Regression test:
  `proofs/soundness/format-latex-argument-parses.kurt`. Making `format
  latex` reachable exposed a further, real, pre-existing bug it had never
  been possible to trigger before: `expr_latex` (the function `format
  latex` actually prints through — a separate code path from `-l`'s own
  document generator) was a stale copy-paste of `expr_normal` that still
  called `expr_normal` recursively and never consulted `kb.get_latex` at
  all, so `format latex` silently printed identically to `format normal`,
  ignoring every `latex SYMBOL REPLACEMENT` declaration. Fixed by making
  `expr_latex` recurse into itself and substitute each operator token
  through `kb.get_latex` (falling back to the symbol's own name). Confirmed
  `-l`'s own LaTeX document generation is unaffected (separate `latexify`
  code path, string-based, not `expr_latex`). Regression test:
  `tests/test_format_latex.py` (needs `mainstream=True`, real printed
  output, so it can't live under `proofs/`, same reasoning as the bracket
  test below).
- ~~**`brackets` leaks its internal sentinel into user-facing output.**~~ —
  **fixed.** `add_brackets`'s `nud` wraps a *custom* bracket pair in an
  operator token named `f'{lbracket}$$${rbracket}'`. `expr_normal`/
  `expr_latex` already had a dedicated case to strip the `$$$` back out for
  *any* declared bracket pair (via `is_bracket_placeholder`), but
  `expr_sexpr` (used by `format sexpr`, and by `parse`/`sexpr` regardless of
  the active format) had no such case, so it printed the placeholder
  literally, e.g. `([$$$] A)` for a user-declared `brackets "[" "]"`. Fixed
  by giving `expr_sexpr` the same bracket-placeholder case, printing e.g.
  `[]` (concatenated left+right) as the s-expression head. Regression test:
  `tests/test_bracket_sexpr_display.py` (a real CLI subprocess run, not a
  `proofs/` file — `parse`'s output is only printed when `mainstream=True`,
  which the auto-discovered `proofs/` harness never exercises since it
  always calls `load_file` with `mainstream=False`).
- **Run a profiler once** ("TODO run profiling") — trivial to just do
  (`python -m cProfile -m kurt.kurt some-proof.kurt`, or profile the test
  suite), and its output would directly inform the several perf todos below
  instead of guessing.
- **"search all TODO in the code and check whether they are still
  relevant"** — there are exactly **two** inline TODO comments left in
  `kurt.py` (corrected count — an earlier pass here said one and missed the
  second): one in `rename_all_vars` ("some are renamed again, this can be
  improved later", a correctness-preserving redundancy, not a bug), and one
  in the `sub`-decomposition matching code (`generate_all_combinations`'s
  caller, "in this case we should do something more sophisticated" —
  matching against a compound `sub $x $a F %A`-style pattern where `F` is
  itself an applied function symbol isn't attempted, only the simpler case
  is). This task is basically already done; both remaining comments are
  low priority (real gaps in matching completeness, not soundness bugs —
  a missed match just means a derivation fails, not that a wrong one
  succeeds), noted here rather than actioned.
- **Re-check `tutorial/*.kurt` and `doc/*.md` for staleness, with a fresh
  reviewer (no memory of this session's changes).** A long run of soundness
  fixes landed in one sitting (hardcoded `forall`/`exists`, the `expect`
  keyword, `sandbox`/`break` unification, the bare-`%`-schema-axiom warning,
  `equal_expr` alpha-equivalence, `add_arity`/`add_bindop` ancestor checks,
  the exit-code fix, the `local`/selective-export feature, ...) and each was
  cross-checked against the docs *at the time*, but a session-long thread of
  small edits is exactly the condition under which something gets missed or
  a cross-reference quietly goes stale. Worth a dedicated pass by a reviewer
  starting cold — reading `tutorial/*.kurt` end to end as a learner would
  (note: there is no tutorial lesson for `local` yet, since it landed after
  the tutorial was written — that's a real gap, not an oversight to
  cross-check), and `doc/kurt-doc.md`/`kurt-soundness.md`/`dev-notes.md` for
  accuracy against current
  `kurt.py` behavior — rather than someone who already knows what "should"
  be there.
- ~~**Lexer greedily merges adjacent "standard operator" punctuation
  characters, including bracket characters**~~ — **fixed.** Found while
  retrofitting `natural.kurt` for the `local`/export feature: `{0, 1, 2,
  ...}` (no space before the closing brace) lexed `...}` as *one* symbol,
  silently swallowing the closing brace. The immediate, worse-than-a-parse-
  error consequence: the resulting unclosed bracket left the parser
  permanently "waiting for a continuation" that never arrives, and
  `read_eval_loop` just breaks out of its loop on EOF while in that state —
  silently discarding the *entire rest of the file*, no error at all. Fixed
  by giving bracket characters (`{`/`}`/`[`/`]`) their own always-single-char
  regex alternative, matching how `(`/`)` were already handled, instead of
  sharing the greedy multi-character "standard operators" class. Confirmed
  the fix doesn't affect genuinely multi-char operators (`<=`, `>=`, `!=`,
  ...), and that `{`/`}`/`[`/`]` still work fine as ordinary punctuation
  before any `brackets` declaration exists (they're just never eligible to
  merge with neighbours either way now). See `doc/kurt-soundness.md` §7 and
  `proofs/soundness/bracket-adjacency-lexes-correctly.kurt`.
- ~~**A much more general version of the same failure mode: EOF mid-statement
  silently truncated the file**~~ — **fixed.** Found immediately after fixing
  the lexer bug above, by asking "is silently swallowing the rest of the
  file on EOF really specific to that one lexer bug, or could *any*
  genuinely unclosed construct trigger it?" It could: `read_eval_loop`
  broke out of its loop on EOF unconditionally, with no check for whether a
  statement was still mid-parse (`continued == True`) — so a plain typo
  (forgetting to close a bracket, anywhere, for any reason) silently
  discarded everything from that point on and reported `Proof checked`,
  exit code 0. Fixed by raising a clear `ParseError` instead of breaking in
  that case. See `doc/kurt-soundness.md` §7.2 and
  `proofs/soundness/eof-mid-statement-rejected.kurt`.

## Testing-infrastructure issue — now has a real fix (`expect`), partially retrofitted

- **`tests/test_kurt_proofs.py` silently truncates failed-proof comparisons
  to 17 characters.** Found while checking todo.md's "put lots of negative
  proof examples into tests/proofs" and "test the conditions for forall and
  exist rules". The harness (line 72-75) does:
  ```python
  if actual_last_line == true_last_line:
      self.assertEqual(actual_last_line, true_last_line)
  else:
      self.assertEqual(actual_last_line[:17], true_last_line[:17])
  ```
  So for a proof file whose expected marker is an error message, the test
  only actually checks the first 17 characters — the rest of the message
  can drift silently forever without the test ever failing or being
  noticed. **Fixed for the cases that fit it**: a new `expect "KIND"`
  keyword (`kurt.py`, see `doc/kurt-doc.md` §9.6) lets a `.kurt` file assert
  *inside itself* that a step raises a given error kind — matching
  `KurtException.kind`, not comparing message text at all — so the file
  either fully succeeds (`;;; Proof checked.`, no marker fragility) or
  fails for real. Retrofitted: `forall-elim-fail.kurt`,
  `proofs/debug/mini-again.kurt`, `tutorial/46-calc.kurt`, plus a new
  `tutorial/16-expect.kurt` lesson. **Three files still rely on the 17-char
  fallback, deliberately**: `proofs/debug/load-cycle-a/b.kurt` need to match
  the error *kind* across two different files' absolute paths, which
  `expect` can't do for a cycle that spans files (the cycle gets "caught"
  one file too early if either side wraps its own `load` in `expect` — a
  real, checked limitation, not an oversight); and
  `proofs/debug/test-not-all-blocks-close.kurt` is testing a truncated
  file with no body to wrap in a block at all. The harness's 17-char
  fallback itself is unchanged and still needed for exactly those cases —
  todo.md's "put lots of negative proof examples in tests/proofs" should
  reach for `expect` first and fall back to the marker convention only when
  `expect` genuinely doesn't fit (spans files, or tests malformed structure
  rather than a failing statement).
- ~~**Every `expect`-using file still had to spell out `;;; Proof checked.`
  anyway**~~ — **fixed.** All 12 `expect`-using files under `proofs/` (the
  two under `tutorial/` don't use the marker convention at all, see
  CLAUDE.md) had this exact, identical, information-free marker line —
  `expect` already checks the interesting condition internally, so the
  marker was pure boilerplate in every single case. `file_last_line`
  (`tests/test_kurt_proofs.py`) now allows omitting the marker specifically
  when the file contains a real `expect` statement (detected by scanning
  non-comment lines — `expect` is a reserved keyword, so this can't
  false-positive on a user identifier), defaulting to `'Proof checked.'` in
  that case. A file with *neither* a marker *nor* `expect` raises a clear
  `AssertionError` from the test setup itself (not a silent pass) — the
  point is removing retyped boilerplate, not weakening "every `.kurt` file
  under `proofs/` must actually assert something." Stripped the now-dead
  marker line from all 12 files. See `tests/how-to-write-test-proofs.md`.

## Concrete, medium-effort feature/robustness work

- ~~**"solve the path puzzle, also check `load ../foo.kurt`"**~~ — **done.**
  Added concrete regression coverage for everything this todo asked for:
  `proofs/debug/load-relative/uses-subdir.kurt` (`load sub/inner.kurt`) and
  `sub/uses-parent-dir.kurt` (`load ../helper.kurt`) confirm relative-path
  resolution goes both directions from a loaded file's own directory, not
  just cwd/`theory_path`; `proofs/debug/load-diamond.kurt` confirms a
  *diamond* dependency (`equality`+`logic` both `load prop`) is genuinely
  cycle-safe and doesn't double-load (this was already incidentally
  exercised by `set.kurt`, part of the auto-discovered theories, but wasn't
  an explicit, direct test before); `proofs/debug/load-cycle3-{a,b,c}.kurt`
  extends the existing 2-file cycle regression to a 3-file chain, confirming
  `_loading_in_progress`'s check isn't accidentally hardcoded to exactly one
  back-and-forth. No code changes needed — all of this already worked.
- ~~**Merge `pick`'s parsing into `unpack_condition`**~~ — **done, but
  deliberately not full symmetry with `let`.** ("allow `let x with F(x)`,
  ... merge `pick` and `let` to use `unpack_condition`") `pick`'s new-const
  parsing now goes through `unpack_condition`, same as `let`'s — genuine
  code sharing, better/consistent error messages (e.g. `pick f with P f`
  for an already-declared `f` now says so specifically, instead of the
  generic "takes a new constant, keyword `with` and a formula"). The
  bigger discovery along the way: `pick`'s args never go through
  `parse_expression` at all (`pick` isn't in `keywords_with_parsing`, see
  `parse_tokenstream`) — they're still a *flat list of raw tokens*, split
  only on top-level commas, with `with` marking where the new-constant part
  ends and the fact begins. So the merge is: find `with`, and if exactly
  *one* raw token precedes it, feed that one token through
  `unpack_condition` (trivial for a bare token, but the same code path
  `let` uses); more than one token before `with` now gets its own specific
  "does not support an extra condition" error instead of falling through
  to the generic message.
  Explicitly did **not** implement the todo's literal "`pick x>0` works
  symmetrically to `let x>0`" ask, after actually thinking through what it
  would mean: `let x>0`'s condition becomes an *assumption*, discharged
  (quantified away) when the block closes (§9.2) -- it's sound precisely
  because nothing is asserted about `x` outright, only "if x>0, then...".
  A `pick`ed witness is different in kind: it's *existential*, introduced
  because some `exists $x P` is already known to hold for *some* value,
  with `FACT` (`P` with the witness substituted in) as its only
  established property. Accepting `pick x>0 with FACT` would silently add
  `x>0` as an unproven, unquantified fact about that one witness -- a
  soundness hole, not a convenience, since nothing ever justified `x>0`
  specifically. `unpack_condition`'s condition-branch is deliberately kept
  reachable in the code (`assert`ed unreachable would be wrong, since
  nothing currently prevents a future parsing change from producing a
  compound pre-`with` expression) but always rejected with a clear error
  naming the reason, rather than silently ignored or silently accepted.
  Similarly did not add a symmetric `with`-clause to `let` itself --
  `let`'s existing inline condition (`let x>0`) already covers the same
  need `pick`'s `with` covers for `pick`, so a second syntax for the same
  thing would just be redundant, not an actual gap.
  Regression test: `proofs/debug/pick-error-messages.kurt`. Documented in
  `doc/kurt-doc.md` §9.3.
- ~~**`f()` (zero-argument call) doesn't parse**~~ — **done.** ("why not
  `f()`??? what is it? it should be parsed `(f)` instead of just `f`") The
  original `todo.md` wording actually already answers its own "design
  decision" question, once read literally: `f()` should parse the same as
  `(f)` -- and `(f)`, once `remove_round_brackets` strips its purely
  grouping parens (as it already does for any `(EXPR)`), is *exactly* bare
  `f`. So the target was never a distinct "0-arg application node" (as
  `todo-claude.md`'s own earlier, more speculative note here guessed) --
  just "`f()` means `f`," full stop.
  Two changes: (1) `add_brackets`'s `nud` now accepts an empty body (peeks
  for the closing bracket immediately after the opening one) instead of
  unconditionally calling `parse_expression` first and choking on it --
  returns a bracket-placeholder node with an empty tail rather than
  raising `SyntaxError: token ')' cannot start an expression`. This alone
  makes `()`/`{}`/etc. parseable wherever a bracket is legal, not just
  after a symbol. (2) `process_arity`/`group_by_arity` give that empty
  node a meaning specifically when it directly follows a symbol: for an
  arity-0 symbol, drop it entirely (`f()` and `f` produce the identical
  parsed `Expr`, confirmed by their log lines printing identically and by
  `parse f()` / `parse f` printing the same sexpr); for a symbol with a
  declared arity of 1 or more, raise a clear, specific `EvalError` ("empty
  parentheses `()` cannot supply an argument for `f`, which needs N
  argument(s)") rather than letting the empty-bracket node silently become
  a nonsensical "argument value" (which is what `group_by_arity`'s
  existing greedy consumption would otherwise have done, unnoticed).
  Verified this doesn't regress ordinary calls (`f(x)`/`f a` still work
  identically) and doesn't crash on a bracket with no preceding symbol at
  all (`parse ()`) -- it just parses to a standalone empty-bracket node,
  which is a new but harmless parseable shape, not a new axiom or
  soundness-relevant construct.
  Note on methodology: initially verified this in a scratch copy under a
  separate `PYTHONPATH`, which produced 3 unrelated test failures
  ("symbol already exists") that turned out to reproduce identically with
  a completely *unmodified* copy of `kurt.py` under that same scratch
  path -- an artifact of running the test suite against a package copy
  outside the editable install, not a real regression. Confirmed clean
  (`OK`, 95/95) once applied to and tested against the real repo via the
  normal `PYTHONPATH=src python3 -m unittest`.
  Regression test: `proofs/debug/zero-arg-call.kurt`. Documented in
  `doc/kurt-doc.md` §4.3.
- ~~**"do checks for `case` statements"**~~ — **investigated; resolved as a
  documentation gap, not a code one.** `case` is handled completely
  identically to `assume` everywhere, confirmed — there is no case-specific
  validation, and there's no clean way to add real exhaustiveness checking
  without new cross-statement state (`case` blocks aren't tracked as a
  group at all; each is popped independently, and the final `or-elim`
  combination is just an *ordinary* derived fact, requiring the user to
  have separately `use`d the real disjunction and to explicitly restate the
  goal after the cases close — see `doc/kurt-doc.md` §9.1, now spelled out
  precisely). Crucially: this is **not a soundness gap** — `or-elim` always
  needs the genuine disjunction fact to fire, so a missing "case" simply
  makes the proof fail to complete (an ordinary "can not derive" on the
  final restated line), it never accepts an unsound one. Given that,
  building real exhaustiveness checking would only improve error-message
  clarity, not correctness — a real but lower-value feature than it first
  sounds, so left undone; documented the two actual prerequisites clearly
  instead (`doc/kurt-doc.md` §9.1, `tutorial/21-case.kurt`), which is
  exactly what would have saved time debugging
  `proofs/mafi1/001-two-equal-sets.kurt`'s missing disjunction fact
  earlier this session.
- ~~**Quantifier variable-kind check**~~ — **investigated and resolved, no
  code change needed.** Confirmed (see `doc/kurt-soundness.md` §6) that
  `let`'s boolean/non-boolean handling doesn't add or remove any
  exploitability: a bare `use %A implies P` (no `let` involved at all)
  already makes `P` unconditionally derivable, and this is an inherent,
  by-design property of `%`-prefixed schema variables in `use` statements,
  not a `let`-specific gap. A real, unrelated bug turned up during this
  investigation instead — see `doc/kurt-soundness.md` §2.2 (now fixed).
- ~~**`def`'s LHS-appears-once check likely has gaps**~~ — **investigated
  and fixed.** `extract_by_condition` (used by `def`'s LHS/RHS scan) had no
  bound-variable awareness, confirmed on both sides: RHS wrongly *rejected*
  a plain (non-`$`-prefixed) bound variable as a disallowed new symbol, and
  LHS could wrongly *accept* a def whose "new constant" was actually just a
  quantifier's own bound variable (harmless in practice — it never actually
  became a real constant — but a misleading pass). Both fixed by making
  `extract_by_condition` bound-variable-aware, mirroring `contains`. See
  `doc/kurt-soundness.md` §3.1 and
  `proofs/soundness/def-bound-var-not-new-symbol.kurt` /
  `def-lhs-bound-var-rejected.kurt`.
- ~~**`save` command**~~ — **done.** ("have a `save` command that stores the
  current theory and state") Resolved the open design question ("what does
  'state' mean?") as: syntax declarations + theory facts, from every level
  below (and including) the current one, excluding level 0 (the pristine
  hard-coded core, already present in any fresh session) and excluding the
  level stack itself (a pending `show`/open proof block has no sensible
  flat representation — `save` is meant to be called once everything's
  settled). New function `save_state_str`, reusing the existing per-level
  `dict_or_set_str` printers for syntax but writing its own theory-fact
  loop rather than reusing `theory_str` (which prints a proven fact bare,
  with no `use`, since it's meant for human display, not reload) — every
  fact is re-emitted as `use`/`def`/`todo`, however it was originally
  obtained, so reload never re-runs a proof search. Two non-obvious
  ordering/registration issues found by actually round-tripping the output
  through `load` (not just eyeballing it):
  1. `const` declarations must be omitted entirely -- operator/constant
     symbols auto-register the first time they're used (in a syntax
     declaration or a formula), exactly like `prop.kurt` itself never
     writes `const not`/`const or`; emitting an explicit `const` line
     ahead of that auto-registration collided with it.
  2. syntax categories must be written in a specific order -- `bool` before
     `chain`, since `chain` immediately synthesizes and `use`s transitivity
     formulas mentioning the operator (`generate_chain_transitivity`),
     which would otherwise mark it "already used" before its own `bool`
     line runs.
  Also: every fact gets a label, synthesizing `"save-N"` for one that
  didn't already have one -- otherwise it would work when the saved file is
  run directly but silently vanish (per ordinary `load` selective-export
  rules, see doc/kurt-doc.md's `load` section) the moment that file is
  instead `load`ed from somewhere else, defeating the point of saving it.
  Along the way, round-tripping surfaced and fixed a genuine, independent
  printer bug: `expr_normal`/`expr_latex` never parenthesized a plain
  (arity-processed) function call (`f a`) when it appears as a *sub*-term
  of a tighter-binding infix operator, so e.g. `f a ∈ B` printed as
  literally `f a ∈ B` -- which then re-parses as `f (a ∈ B)` (application
  binds looser than `∈`), silently changing the formula's meaning on
  reload. Every other node shape already added its own parens; only the
  bare 2-element call case didn't. Fixed in both `expr_normal` and
  `expr_latex`. Also fixed `syntax_str_all_levels` to include `nonassoc`
  syntax declarations (`add_nonassoc` didn't have display coverage
  before). Also fixed a stale test exemption in
  `test_theory_syntax_survives_load.py`: `set.kurt`'s `→` used to be
  exempted as "genuinely unaxiomatized," which stopped being true once
  this session's `function-space`/`function-extensionality` work (see the
  `set.kurt` entry above) gave it a real axiom -- the test now actually
  checks it. Regression tests: `tests/test_save_command.py` (round-trips
  `save`'s own output through `load` into a fresh session and checks both
  a labelled and a synthesized-label fact survive; a second test exercises
  `chain` + the function-application-in-`set.kurt` case together).
  Documented in `doc/kurt-doc.md` §8.2 (`save`, right after `load`'s "What
  gets exported").
- ~~**`sandbox` can commit**~~ — **done.** ("have a `sandbox` block, where we
  first try and try, and then store it to the theory") New keyword
  `commit`: closes a `sandbox` immediately (no dedent needed, exactly like
  `break`) but keeps its content instead of discarding it, via the same
  mechanism `load` already uses for cross-file export — `KnowledgeBase.
  merge_and_pop()` — so it's selective export, not "keep everything": only
  a labelled, non-`local` fact (and the symbols it needs) survives, an
  unlabelled one stays scratch even after `commit`, exactly as it would in
  a `load`ed file. Restricted to only ever close a `sandbox` (every other
  block already has its own way to keep what happened inside on close, so
  `commit` on one of those is rejected with a clear error rather than
  silently doing something else via `merge_and_pop`, which isn't built for
  those block kinds' own semantics).
  Along the way, found and fixed a real, independent, pre-existing crash:
  `break` (and now `commit`) at the very top level of a file — not inside
  any `sandbox` the file itself opened — used to trigger an internal
  `assert False: BUG: load_file decreased the level` instead of a clean
  error. Cause: running a file, or `load`ing one, already starts one level
  deep inside an *implicit* `sandbox` `load_file` itself pushes (see
  doc/kurt-doc.md §8.2/§9); `break`/`commit` had no way to tell that hidden
  wrapper apart from a real, user-written `sandbox` block, so a bare
  `break`/`commit` typed at a file's top level happily closed the wrapper
  out from under `load_file`, which expects to be the only thing popping
  that exact level. Fixed with a new marker,
  `KnowledgeBase.is_load_boundary` (set only on that implicit level, and
  excluded from `merge_and_pop`'s generic attribute-merging loop like
  `tmp`/`var`), which `break`/`commit` now check first and refuse with a
  clean `EvalError` instead of touching that level at all.
  Regression tests: `proofs/debug/commit.kurt` (positive: a labelled fact
  survives `commit`; negative control: the same shape without `commit`,
  via plain `break`, does not), `commit-unlabelled-fact-does-not-export.kurt`
  (an unlabelled fact stays scratch even after `commit`),
  `commit-only-closes-sandbox.kurt` (`commit` inside a `proof` is
  rejected), `commit-and-break-reject-file-top-level.kurt` (the crash fix).
  Documented in `doc/kurt-doc.md` §9.4/§9.5.
- ~~**Chains don't generate real transitivity**~~ — **done.** `chain` used
  to only affect *parsing* (deciding which operator a written continuation
  line desugars to). Declaring `chain OP1 OP2 ...` now *also* generates a
  real, directly-usable transitivity axiom for every ordered pair of the
  chain's operators (`generate_chain_transitivity`, hooked into the
  `chain` keyword's own handler) — reusing exactly the same "pick the
  operator with the larger index" rule the parsing sugar already used, now
  applied to two *separately-proven* facts rather than one written
  expression. Implemented by synthesizing `.kurt` source text for each
  generated axiom and feeding it through the ordinary `read_eval_loop`
  pipeline (not hand-built `Formula`/`Expr` objects) — reuses all the
  existing label/type-check/export bookkeeping for free. One real
  complication: a chain's variables need `%`-prefixed (boolean) schema
  names for a connective chain (`iff`/`implies`) but `$`-prefixed
  (non-boolean) ones for a relation chain (`<`/`<=`/`=`) — resolved by
  checking `kb.bool_sig(op)` for whether argument positions are marked
  boolean. `arith.kurt` no longer hand-writes its 8 transitivity lemmas
  (`lt-trans`, `le-lt-trans`, ...) — they're generated automatically from
  its existing `chain = <= <` / `chain = >= >` now. Verified all 8 replaced
  cases plus `equality.kurt`'s `chain =` and `prop.kurt`'s
  `chain iff implies`/`chain iff invimplies` (a nice side effect: plain
  `A implies B` + `B implies C` → `A implies C` now needs no manual
  intermediate step either, chipping away at the general single-hop
  limitation for exactly this one shape). 2 new regression tests under
  `proofs/soundness/`. Adversarial testing while checking this over
  surfaced an unrelated, pre-existing type-checking laxness — see the
  "needs investigation" entry above; confirmed via `git stash` to have
  nothing to do with this change.
- ~~**Extend `calc` beyond `+`/`*` on ints**~~ — **this note was stale/wrong,
  corrected while working through the theory-completeness pass.**
  `KnowledgeBase.calculate()` already handles `-` (unary and binary), `/`,
  and `^` on Python `int`/`float` tokens, not just `+`/`*` — confirmed
  directly while writing `proofs/arithmetic/factorial-recursion.kurt` and
  `exponent-laws.kurt`, both of which rely on `calc` reducing `-`. What's
  still genuinely open: no explicit handling of floating-point
  precision/equality (e.g. `0.1 + 0.2 = 0.3` would compare the raw Python
  float result, no tolerance), which is a real, separate, much smaller
  remaining item than the original (inaccurate) note implied.
- ~~**`$$`-prefixed internal names could collide with user variables**~~ —
  **checked, turns out to be a non-issue.** My earlier claim here was wrong:
  I said "a user *can* type a variable named literally `$$foo`" without
  actually trying it. The lexer's `SYMBOL` pattern (`scanner`, kurt.py) is
  `[$%@]?[A-Za-z][A-Za-z0-9]*` — at most *one* leading `$`/`%`/`@`,
  immediately followed by a letter. `$$foo`/`%%foo` fail to match that (or
  any other branch) and hit the lexer's catch-all `ERROR` group instead,
  raising a `SyntaxError` before parsing even starts — confirmed directly
  (`var $$foo` → `SyntaxError: scanning error while scanning \`$\``). So
  `new_var_name()`/`new_bool_var_name()`'s doubled-prefix scheme is safe by
  *construction* (no source text can ever lex into such a token), not merely
  by convention as the old comment implied. No code change needed; locked in
  by `proofs/soundness/dollar-dollar-prefix-unparseable.kurt`.
- **~~Audit `minimal.kurt` against its hard-coded Python counterpart~~ —
  done.** Confirmed the mismatch: `"restatement"` (`$A implies $A`) and a
  general `"impl-intro"` schema were drafted as if hard-coded but aren't
  reachable as standalone facts (`A implies A` doesn't derive from
  nothing). Rewrote `minimal.kurt`'s inference-rules section to describe
  only what's actually hard-coded (`top-intro`, `impl-elim`, `and-intro`,
  and `impl-intro`/`not-intro` as the *effect* of closing an `assume`
  block, not standalone axioms), with an explicit note on what was removed
  and why, and pointers to how to get the same result the real way
  (`show`/`proof`/`assume`/`qed`, or `load prop` for a general
  `not-intro`). Also fixed: the old `not-intro` line referenced `not` and
  `false`, neither of which `minimal.kurt` itself ever declares.

## Larger, well-defined refactors (bigger, but not vague)

- **~~Turn `KurtException`'s string-prefix "types" into real types~~ — done,
  as a cheap hybrid rather than the full mass-edit.** `KurtException` now
  has a `.kind` attribute (one of `KurtException.KNOWN_KINDS` =
  `('ProofError', 'ParseError', 'EvalError', 'SyntaxError', 'TypeError')`,
  or `None`), auto-derived from the existing string prefix in `msg` at
  construction time. Deliberately *not* done: rewriting all ~130
  `raise KurtException(f'XError: ...')` call sites to pass `kind=`
  explicitly — auto-derivation gives the same reliable `.kind` attribute
  (now used by `expect`, §9.6 of `kurt-doc.md`) with none of the risk of a
  130-site mechanical edit for no behavioural gain. A handful of messages
  don't start with a recognised prefix (e.g. `check_all_shown_proved`'s
  "Not shown:\n..." message) and get `kind=None` — acceptable, rare, and
  honestly unclassified rather than silently wrong. Revisit the full
  subclass/explicit-`kind` version only if `.kind is None` actually starts
  causing real problems somewhere.
- **Data structure for the theory, indexed by conclusion** ("organize the
  implications as a dictionary of lists with the top-level operator of RHS
  as the key"; "instead of brute-force matching, use more clever matching,
  e.g. search for the sub terms, or have a dictionary of all subterms";
  "runtime: `derive_expr` is O(n^k)...") — these three todo items are the
  same underlying performance problem from different angles. Confirmed:
  `derive_expr` (line 3879) and `match_all_theory` iterate `kb.all_theory()`
  linearly, and `generate_all_combinations`/`all_single_hole_decompositions`
  (line 3222-3251) try *every node* of an expression as a candidate
  substitution site. For small proof files (everything in `proofs/` today)
  this is fine; it would degrade badly on a large theory. A concrete,
  incremental first step: index `kb.theory` by the top-level operator of
  each formula's conclusion (RHS of an implication, or the formula itself)
  so `derive_expr` only scans plausible candidates. This is the kind of
  change that needs before/after benchmarks (see "run profiling" above) to
  justify, since it adds real complexity to `KnowledgeBase`.

  **2026-09-09 follow-up sweep, specifically for *other* big-O issues beyond
  the theory-indexing one above** (requested after the `set-comprehension`
  fix). Found four more, all confirmed by reading the actual code, ranked by
  how often the hot path is actually hit:
  1. ~~**`impl_elim` recomputes `free_bound_vars(expr, kb)` from scratch on
     every call, even though `derive_expr`'s own loop calls it with the
     exact same `expr` every single iteration.**~~ — **fixed (2026-09-11).**
     Confirmed at kurt.py:4598 (the `is_iff` third-attempt branch) and
     :4610 (the plain-implication branch) — both recomputed
     `free_bound_vars(expr, kb)[0]` from `expr`, not from anything
     iteration-specific, turning an O(expr size) computation into O(theory
     size × expr size) *per derivation attempt*, on the single most-called
     path in the whole engine. Fixed by computing it once in `derive_expr`
     (before the `for proven_formula in kb.all_theory()` loop) and
     threading it through as a new `expr_free_vars` parameter, including
     through `impl_elim`'s own recursive self-calls for an `is_iff` fact
     (which previously re-triggered the same recomputation again on every
     recursive hop). Pure hoist, no matching-semantics change — confirmed
     via the full suite (95/95) and by re-running both `iff`-eigenvariable
     soundness regression tests directly.
  2. **`unify_exprs_with_patterns`'s flat-and-symmetric-operator branch
     (kurt.py:4297-4317) is combinatorially far more expensive than the
     already-documented decomposition costs** — worse than the fork's own
     first-pass report initially flagged, so re-verified directly: matching
     a schema pattern with `k` variables against a concrete flat+symmetric
     expression (e.g. `and`/`or`) with `n > k` arguments calls
     `partitions(tail_e, k)` (a Stirling-number-of-the-second-kind count of
     ways to partition `n` items into `k` non-empty unordered blocks — much
     worse growth than the flat-*non*-symmetric branch's `split_into_lists`,
     which only tries *contiguous* splits), and then for **every** partition
     additionally runs `itertools.permutations(subset)` over the resulting
     blocks before even attempting unification on each combination. Live
     today, not a future concern — any goal matching a multi-variable schema
     against a longer `and`/`or` chain pays this now (e.g. matching `%A and
     %B` against a flat 5-way `and` already enumerates every 2-block
     partition of 5 elements, times every within-partition permutation).
  3. **`State.bind` (kurt.py:606-610) does `dict(self.subst)` — a full copy
     of the whole substitution dict — on every single variable binding.**
     **Investigated with an actual persistent-map redesign (2026-09-11),
     then reverted after measuring it — this is exactly the kind of
     "obvious win on paper" that turned out not to hold up.** Built a
     `Subst` class (an immutable singly-linked chain of bindings, O(1)
     `extend` instead of O(n) dict-copy) and switched `bind` to use it.
     Result: **no measurable improvement on the actual test suite** (three
     timed runs before/after were statistically indistinguishable, if
     anything a hair slower — plain-`dict` copying of the *small* dicts
     kurt's real proof files ever produce is already fast in CPython, and
     the persistent chain adds Python-level per-node traversal overhead to
     `lookup`, which is called far more often than `bind` ever is). Worse,
     a synthetic stress test (20,000 chained binds then 20,000 lookups)
     showed the *lookup* side degrading to O(chain depth) — 5.7 seconds for
     20,000 lookups against a 20,000-deep chain, vastly worse than dict's
     O(1) lookup — meaning the fix would trade a bounded, guaranteed-small
     cost today for an *unbounded* one in exactly the pathological case
     (many bindings accumulated in one derivation, e.g. a long flat-operator
     chain — the same territory as #2 above) it was meant to help with.
     Reverted `bind` back to plain `dict` copying, with a comment
     explaining why the persistent version was tried and rejected, so a
     future reader doesn't reinvent this without re-measuring.
     **What did survive, and is a genuine, zero-risk, unambiguous win**:
     `block_as_domain`, `block_always`, and `unblock` were each doing a full
     `dict(self.subst)` copy too, despite never touching `subst` at all —
     confirmed no code anywhere mutates a `State.subst` dict in place (only
     `.get()` reads and full-dict copies existed), so these three methods
     now just pass `self.subst` through unchanged, eliminating 3 of the 4
     redundant copies for free, with no representation change and no
     lookup-cost tradeoff. Full suite (95/95) and the `iff`-eigenvariable
     soundness regressions re-confirmed after landing this.
  4. **Investigated, not implemented — genuinely unsafe as a caching fix,
     not just low-value.** `KnowledgeBase`'s symbol-classification methods
     (`is_var`, `is_const`, `get_arity`, `bool_sig`, `is_infix`, etc.) are
     O(level-stack depth) via `self.parent.is_x(s)` recursion with no
     caching. Traced the actual call pattern before proposing a fix: 
     `_add_new_symbols` (kurt.py:1499-1521, called on *every* symbol in
     *every* expression processed anywhere) does exactly `if self.is_var(s)
     or self.is_const(s): pass; elif not self.is_used(s): ...
     self.add_const(s)` — i.e., it queries `is_var`/`is_const` on a symbol
     immediately *before potentially declaring that exact symbol* in the
     same function call. This is the common case, not an edge case: a
     symbol's first-ever appearance is always a negative lookup immediately
     followed by a declaration. Naively memoizing `is_var`/`is_const`
     results would go stale within the same statement's processing unless
     the cache were invalidated on every one of the ~15 mutating `add_*`
     methods (`add_const`, `add_var`, `add_infix`, `add_bool`, ...) — real,
     error-prone invalidation plumbing for an item this session's own
     report already flagged as "low severity today" (depth is small, a few
     levels in practice). Not worth the correctness risk for the payoff;
     left undone and documented here so a future caching attempt starts
     from this finding instead of re-discovering it the hard way.
- ~~**`nonassoc` operators**~~ — **done.** New `nonassoc OP` keyword
  (mirroring `flat`/`sym`'s existing "declare a property of an already-
  `infix` operator" pattern, rather than extending `infix`'s own argument
  list): `a OP b OP c` now raises a `ParseError` right at the second `OP`
  instead of silently left-associating, while explicit parenthesization
  (either grouping) still works fine. Implemented at parse time (in the
  operator's own `led`, checking whether the token right after the parsed
  right operand is the same operator again), not in `post_process` as
  originally suggested — catches it exactly where the ambiguity is, with a
  precise column, rather than needing a separate later pass. Mutually
  exclusive with `flat` (checked both declaration orders — an operator that's
  inherently associative by construction can't also assert it's ambiguous
  to chain). Regression test:
  `proofs/soundness/nonassoc-rejects-chained-usage.kurt`.
- ~~**`'thus'` keyword**~~ — **done.** ("'thus' with one step shorter, for
  `qed` we use match, for `thus` we use equal") New keyword, `qed`'s
  sibling: closes a `proof` block (only a `proof` — not `assume`/`case`/
  `let`/`pick`, unlike `qed`) by checking the block's last formula is
  *literally* the planned goal, via `equal_expr` (alpha-equivalence-aware,
  the same notion of "the same formula" used elsewhere), instead of `qed`'s
  full `derive_expr` search — cheaper and its outcome is predictable just
  by reading the last line, at the cost of rejecting a last line that's one
  more derivation step short of the goal (`qed` would take that step;
  `thus` won't). Implemented as `eval_thus` (mirrors `eval_qed`'s structure
  exactly, right down the reused `Formula`-carrying-label/local logic), with
  its own dispatch branch in `scan_parse_check_eval` (mirroring `qed`'s: a
  parse-time "must have a real dedent" check, then a dry-run block-mode
  check restricted to `proof` only) since — like `qed` — closing is
  special-cased ahead of the ordinary `eval_keyword_expression` dispatch.
  Also removed `eval_qed`'s long-dead commented-out "option 2" sketch
  (a `unify_exprs_with_patterns`-based alternate design) now that `thus`
  covers that use case for real. Regression tests: `proofs/debug/thus.kurt`
  (positive: last line is literally the goal) and
  `proofs/debug/thus-rejects-non-literal-match.kurt` (negative: last line
  is one `impl-elim` short of the goal, `qed` would accept it but `thus`
  correctly rejects it — uses the older `;;; ` marker convention, not
  `expect`, since the failure happens while `thus` itself closes the block,
  same reasoning as `forall-intro-rejects-leaked-constant.kurt`). Documented
  in `doc/kurt-doc.md` §7 and §9's keyword-listing paragraph.
- ~~**`Formula.origin`**~~ — **investigated; based on a misunderstanding,
  nothing to build.** `Token.origin` isn't a general provenance field — it
  specifically stores the user's originally-*typed* alias name (e.g. `∈`)
  so display can show it back instead of always printing the canonical
  name (`in`), see the scanner's `SYMBOL` case. It has nothing to do with
  "which file did this come from." `Formula` already has `.filename`/
  `.line` for exactly that, actively used already (`formula_ref`'s
  cross-file `by "file.kurt:42"` reason strings, `theory_str`'s printing) —
  the thing this todo asked for already exists under a different name.
- ~~**File-local variables / explicit theory export**~~ — **implemented.**
  ("variables and syntax should be file only... problem: how to show
  formulas that are imported"; "define what gets exported when loading a
  file, make variable declarations local"; "local and export features,
  files should open a new level, but can export statements as axioms to
  the level above them"). Along the way (before the design was settled),
  investigated whether two theories redeclaring the same symbol name could
  do worse than clash confusingly — couldn't turn it into an accepted false
  proof, but found and fixed a real bug: `add_arity`/`add_bindop` only
  checked the *current* level's own dict for "already declared" (unlike
  every other `add_*` method), so redeclaring a symbol's arity across two
  separately-`load`ed files silently overwrote it with no error. See
  `doc/kurt-soundness.md` §4.1.

  The design settled on (worked out in conversation, then implemented):
  a `use`/`def` axiom or proved theorem is exported by `load` exactly when
  it carries a label that isn't marked `local` (new syntax: `EXPR local
  "label"`); an unlabelled fact defaults to not-exported. A symbol has no
  export marking of its own — it's exported exactly when some exported
  fact's free symbols actually mention it, computed automatically (no need
  to separately declare "this symbol is local/exported"). A `local`-marked
  `def` whose symbol is still needed by an exported fact is a load-time
  error, not a silent promotion or a silently-broken symbol. See
  `doc/kurt-doc.md`'s `load` section and `doc/kurt-soundness.md` §7 for the
  full writeup, including two real bugs found while implementing the
  closure computation (aliases, custom brackets) and a third, unrelated
  pre-existing bug found and fixed along the way (`natural.kurt` was
  silently broken, via a lexer token-adjacency issue nobody had ever hit).

- ~~**More proof-suite coverage for arith/set/modal**~~ — **done, partial.**
  Checked which axiom *labels* declared in `arith.kurt`/`set.kurt`/
  `modal.kurt` were never cited by any proof file's derivation (a stand-in
  for "never actually exercised," same idea as
  `test_theory_syntax_survives_load.py`'s operator-coverage check, but for
  axioms). Found most of `arith.kurt`'s order-preservation/algebraic-
  identity/equation-substitution axioms (~48 of 60 labels) had never been
  used by any proof, plus modal's "K"/"diamond-distrib-or" and set's
  "power-set". Added `proofs/arithmetic/algebraic-identities.kurt`,
  `order-preservation.kurt` (each `arith.kurt` order-preservation
  demonstration wrapped in its own `sandbox` so contradictory assumptions
  used for different demonstrations — e.g. `c > 0` vs `c < 0` — don't leak
  into each other), `proofs/modal-logic/diamond-distrib-or-and-k.kurt`, and
  `proofs/set-theory/power-set-membership.kurt` (the last one is the
  "partial": couldn't get the empty-set case to close, see the
  `set-comprehension` finding directly below). Deliberately didn't chase
  every one of the ~48 remaining arith labels individually — the added
  files establish the pattern (restate the schema generically, or combine
  with a `use`d premise) for whoever wants to extend it further; exhaustive
  one-file-per-label coverage wasn't the point.

## Needs investigation before it's clear what "feasible" even means

- ~~**`set-comprehension` doesn't match when the comprehension's body has
  zero occurrences of the bound variable**~~ — **traced and fixed
  (2026-09-09).** Confirmed the suspected root cause exactly:
  `generate_all_combinations`'s decomposition mechanism
  (`all_single_hole_decompositions`) only ever proposes a `%A` by picking
  one existing node of the concrete expression and replacing it with the
  substitution marker — every candidate it can produce has *exactly one*
  occurrence of the marker, so "zero occurrences, `%A` equals the
  expression unchanged, `$a` unconstrained" was never tried at all. Fixed
  by adding exactly that missing candidate. Turns out this restores
  behavior `tests/test_gen_all_combinations.py`'s own `old_examples` (dead
  code, never run) already expected before an earlier performance
  simplification silently dropped it — good independent confirmation this
  was a real regression, not a novel gap. Full writeup, including why this
  is a *different* root cause from the lambda-calculus identity/currying
  gaps (which remain genuinely open, confirmed still failing after this
  fix), in `doc/kurt-soundness.md` #6. Regression tests:
  `tests/test_gen_all_combinations.py`, `tests/test_generate_all_combinations.py`
  (unit-level), and the empty-set-case lines now added to
  `proofs/set-theory/power-set-membership.kurt` (proof-level, the original
  motivating example this was found from).
- ~~**New finding: a declared-but-otherwise-unconstrained `var` can get
  treated as boolean anyway.**~~ — **investigated; turned out to be a real
  soundness bug (a second instance of the forall-elim bug class), now
  fixed — but not the bug the symptom's own framing suggested.** Minimal
  repro (`load prop` / `var a` / `bool C` / `a iff C`) really does "derive"
  `a iff C` for two totally unrelated symbols, citing `"not-not"`. But
  chasing *why* showed the auto-boolean-inference itself is correct,
  intentional, load-bearing behavior (confirmed by trying to tighten it —
  requiring `not kb.is_var(s)` before inferring — and watching four
  legitimate proofs break, including
  `proofs/natural-deduction/and-sym.kurt`, which declares `var a, b` and
  relies on exactly this inference as an alternative to `%`-prefixed
  schema variables). The bare schema variable case (`%A iff C`, no `var`
  at all) reproduces identically, proving the `var`/boolean angle was
  never the cause. Real root cause: `impl_elim`'s handling of an
  `iff`-shaped fact has a "third attempt" (direct match against the whole,
  unstripped fact, e.g. `not-not`'s `%A iff (not (not %A))`) that — unlike
  its other two attempts, which recurse into the plain-implication branch
  and *do* block the goal's own free variables from being assigned during
  matching — unifies the goal directly with the caller's state completely
  unblocked, letting a goal's free variable (`a`/`%A` above) be bound
  straight to `not (not C)`, satisfying the axiom's shape for *some* value
  never asserted to hold. Same class of bug as the forall-elim finding
  (§0 above): a variable meaning "this specific, if arbitrary, value" gets
  unified away instead of required to hold as stated. Fixed by adding the
  identical blocking to the third attempt. Full write-up, including why a
  caller can't fix this by pre-blocking (derive_expr's rename-to-fresh-name
  step uses a global, non-content-addressed counter, so a pre-computed
  blocked name never matches what's actually being unified against) in
  `doc/kurt-soundness.md` §0b. Regression tests:
  `proofs/soundness/iff-third-attempt-blocks-eigenvariable.kurt` and
  `iff-third-attempt-still-works-legitimately.kurt`.
- ~~**"why (not x in emptyset) not working?"**~~ — **now has a concrete
  repro, a diagnosis, and (as of the `set-comprehension` fix above) half of
  it now actually works.** (2026-09-09.) `load set` / `const x` / `not (x in
  emptyset)` still fails to derive on its own — expected, since `emptyset`'s
  definition (`def ∅ = { $a | false }`) is a single `def`-equality, and
  turning `x in emptyset` into `x in {$a|false}` needs an explicit
  `equal-elim` step of its own (the general single-hop limitation, see the
  "automatically iterate over all implications" entry below — this half is
  a real, separate, still-open feature gap, not a bug). But the *other*
  half — `x ∈ {$a|false} ≡ false` itself, which used to fail too, since it
  hit exactly the `set-comprehension` zero-occurrence gap documented above
  — now derives, since that gap is fixed. So the full chain (`load set` /
  `const y` / `y ∈ {$a|false} ≡ false` / `∅ = {$a|false}` / `y ∈ ∅ ≡ false`)
  works today, just still as three explicit hops rather than one automatic
  derivation — see `proofs/set-theory/power-set-membership.kurt`'s
  empty-set-case lines.
- **"automatically iterate over all implications, in particular convert `≡`
  into two implications"; "iterate over the formulas in theory and over all
  conclusions (RHS of implications) as well"; "better inference rules...
  when iterating through `all_theory()` also iterate over RHS of
  implications where the LHS is part of the theory"** — these three
  describe the same real limitation (confirmed: `derive_expr` does one hop
  of `impl_elim` per call, so a two-step chain like `A`, `A implies B`, `B
  implies C` needs `B` to be derived as its own explicit line before `C`
  can follow — see `tutorial/03-implies.kurt`'s comment about this). Turning
  this into automatic multi-hop search is a real feature, but it directly
  trades off against the performance concerns above (more search per
  formula) and against how errors are reported (today's `by 3, 2` reasons
  are one hop; multi-hop search needs a real proof-search trace, not just a
  reason string). Worth a design spike before implementation.
- ~~**"allow multiple replacement in one step (is that possible?)"**~~ —
  **done (2026-09-25), for the two cases that came up in real proofs.**
  `all_single_hole_decompositions` now also proposes (a) every group of two
  or more (but not all) arguments of a `flat` node as one hole (any subset
  for a `sym` operator, consecutive ranges otherwise), e.g. `1 * 1` inside
  `2 * 1 * 1` for the factorial chain, and (b) every subterm that occurs
  more than once as one hole at *all* its occurrences, which "induction"
  needs for a formula mentioning `$n` several times (Gauss's sum). Groups
  are tried only after all single nodes. Other combinations of occurrences
  are still not tried. Substitution results are normalized again
  (`normalize_expr`) so they compare equal to what the user typed. Cost:
  `2^n` group candidates for an `n`-argument sym node, noticeable on long
  sums (a rewrite inside a 6-term sum takes ~0.4 s instead of ~0.1 s).
  Regression tests: `proofs/debug/flat-group-rewrite.kurt`,
  `proofs/natural-numbers/induction-several-occurrences.kurt`.
- ~~**"check whether we need a version of `equal_expr` that allows bounded
  renaming"**~~ — **yes, and fixed.** Found a real, concrete counterexample:
  `pick`/exists-elim outright rejected a valid witness whenever the
  existential's body had a nested quantifier (`exists x (forall y (R x
  y))`), since `rename_all_vars` renames every bound variable independently
  at storage time and `equal_expr` was pure structural (non-alpha-aware)
  comparison. Fixed by making `equal_expr` alpha-equivalence-aware (only
  bound-variable *names* get leniency; everything else still needs exact
  literal identity). Also turned up an unrelated crash while writing the
  regression test: `pick` failing inside `expect` corrupted the level stack
  (`AssertionError`, not a clean failure) — also fixed. See
  `doc/kurt-soundness.md` §3.3-3.4.

## 2026-09-09 revisit of todo.md

Re-read `todo.md` top to bottom against the current state of this file and
`kurt.py`, since so much of the list above had already absorbed it. Most
remaining lines are either already covered above (just re-confirmed) or are
the vague/philosophical items already called out in "Deliberately left out"
below. Genuinely new or newly-concrete findings from this pass:

- **New finding: `"(%A iff top) implies A" to prop.kurt` has a concrete,
  reproducible motivating example, and it's the same single-hop limitation
  already tracked, not a separate gap.** `load prop` / `bool A` / `use A iff
  true` / `A` fails to derive (`ProofError: can not derive \`A\``) even
  though `top-elim` (`(true implies %A) implies %A`) plus ordinary iff-elim
  would get there in two hops. Confirms the "automatically iterate over all
  implications" entry below is exactly the missing piece here too — no need
  for a bespoke `prop.kurt` axiom once multi-hop search exists; adding one
  now would just be working around the real gap. `mafi1`'s example this todo
  referenced is gone — only `proofs/mafi1/001-two-equal-sets.kurt` remains
  in that directory today, and it doesn't touch `iff`/`top` at all, so
  there's nothing left to cross-check there.
- **The lambda-calculus session (see the theory-completeness entry above)
  directly answers an old, previously-unchecked TOPICS-2.0 item: "should
  substitutions be always boolean (see `type_check_expression`)".** Answer,
  confirmed empirically rather than by reading intent: **effectively yes,
  today** — `match_against_sub`'s schema-decomposition matching (the thing
  that lets a concrete goal be matched against a `sub $x $a %A`-shaped
  pattern) only fires when `kb.is_bool()` holds for the substituted-into
  schema variable; a non-boolean (`$`-prefixed) one falls into a different,
  non-decomposing branch. This is exactly why lambda calculus's bodies must
  be boolean-typed predicates rather than arbitrary terms. Not fixed here
  (a real matching-engine extension, same family as the other decomposition
  gaps above), but the open question in `todo.md` now has a definite,
  demonstrated answer instead of a "maybe" — worth linking the two todo
  items together if `todo.md` is edited.
- **"check if lbp > rbp then left-assoc else right-assoc"** — already
  answered, no code change needed: `infix`'s own help text (`kurt.py` line
  ~373) already states the rule precisely ("lhb > rhb means right
  associative"), and `add_infix` already takes both binding powers as
  explicit, independent parameters from the `infix OP lbp rbp` declaration
  — there's nothing implicit left to "check". Recommend deleting this line
  from `todo.md`.
- **"check conditions in `logic.kurt`"** — already done, just not
  cross-referenced. `logic.kurt` itself carries a detailed "requirements"
  comment block (its own header, right below the axioms) spelling out the
  exact freeness/boundedness conditions for `forall-elim`/`exists-intro`/
  `exists-elim`, and this session's own §0/§0b soundness fixes (see
  `doc/kurt-soundness.md`) are precisely the code catching up to what that
  comment already said was required. Nothing further to check here beyond
  what §0/§0b already cover.
- Everything else remaining in `todo.md`'s "NEXT" and "TOPICS before 1.0/2.0"
  sections that isn't listed as done/investigated above is either (a)
  genuinely open but vague enough to need a design decision from the
  maintainer first (what should be loaded by default, get rid of labels,
  merge `used`/`bool`, frozen `Expr` objects, Token reuse, syntax-vs-theory
  export split, `x<y<=z` chained-relation *syntax* specifically as opposed
  to the transitivity semantics already generated, namespaces, refactor the
  `mainstream` flag) or (b) a pure performance item already tracked under
  "Larger, well-defined refactors" above (the theory-indexing idea, the
  equal-elim short-cut idea, profiling). None of these got a deeper look
  this pass beyond confirming they're still accurate as stated — they're
  intentionally left for `todo.md` itself to keep tracking rather than
  duplicated here.

## Deliberately left out (too broad / not really a `kurt.py` task)

Vague/philosophical items ("check theories", "make a good verbose mode for
teaching"), pure research directions ("two algorithms: constraint-based vs
substitution-based (W)"), external/infra projects (running under Pyodide,
VS Code / LSP integration — both plausible but each a separate project, not
a `kurt.py` change), and inspirational links (the Terry Tao Lean posts, the
Haskell indentation wiki page) are intentionally not listed above as
"feasible tasks" — see `suggestions-claude.md` for the ones worth carrying
forward as longer-term ideas.
