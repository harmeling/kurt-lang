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
- **`set.kurt`** — reasonably developed (comprehension, extensionality, ∅,
  ∩, ∪, subset, power-set), one substantial real proof already exercises it
  (`proofs/mafi1/001-two-equal-sets.kurt`). One documented, real gap: `:`/`→`
  (mapping notation) has syntax declared but zero axioms — function
  extensionality was never written. Needs design thought, not a quick fix.
- **`induction.kurt`** — empty stub (just a comment + test marker). Needs a
  design decision first: what does a *general* induction principle (as
  opposed to `natural.kurt`'s Peano-specific one) even mean here — strong/
  well-founded induction over `<`? Over an arbitrary well-founded relation?
  Don't fill this in mechanically before deciding what it's for.
- **`lambda-calculus.kurt`** — empty stub. Needs real design work from
  scratch (abstraction/application syntax, beta reduction, substitution
  semantics built on the existing `sub`/binding machinery) — the biggest
  single piece of remaining work on this list.
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

**Also added mid-pass**: every shipped theory file used to open with just a
one-line title comment (`; arithmetic`, `; modal logic`, ...) and nothing
else — no stated scope, no "what this doesn't cover," no pointer to a real
example proof. Now being given a proper header (scope, known gaps, pointer
to a real proof under `proofs/`) as each theory gets touched in this pass:
done for `natural.kurt`. Still needed: `arith.kurt`, `modal.kurt` (both
touched this pass but not yet given the same header treatment),
`prop.kurt`/`logic.kurt`/`equality.kurt` (solid content, never got a real
header at all), `set.kurt` (already has a good inline comment about the
`:`/`→` gap, but no top-level scope summary), `latex.kurt`. Leave
`induction.kurt`/`lambda-calculus.kurt` for whenever their real content
gets written — no point documenting the scope of a file that's still empty.

## Already done / stale (recommend deleting from `todo.md`)

- **"get group.kurt working with constants and with `var x, y, z`"** —
  `proofs/linear-algebra/group.kurt` already declares `var x, y, z` and is
  part of the auto-discovered test suite; it passes today (`python3 -m
  unittest` — 49/49). Nothing to do.
- **"allow boolean expressions for the bound variable for some binding
  operators"** — already implemented: `type_check_expression`'s `bindop`
  case (around line 2900) and `unpack_condition` (line 2150) both handle
  `forall x>0 F(x)`-style conditions. Confirmed working (`tutorial/21-let.kurt`
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
  `tutorial/23-case.kurt`. Todo is stale.
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
  `proofs/debug/mini-again.kurt`, `tutorial/55-calc.kurt`, plus a new
  `tutorial/15-expect.kurt` lesson. **Three files still rely on the 17-char
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
- **Merge `pick`'s parsing into `unpack_condition`** ("allow `let x with
  F(x)`, ... merge `pick` and `let` to use `unpack_condition`") — `let`
  already uses `unpack_condition` and supports `let x>0`-style conditions
  (line 2167). `pick`, by contrast, has its own hand-rolled match on
  `[SYMBOL, SYMBOL('with'), *fact_expr]` (line 2740) and does not go through
  `unpack_condition` at all. Unifying them so `let x with F(x)` and `pick
  x>0` both work symmetrically is a well-scoped, localized change (touches
  `eval_let`, `eval_pick`, and the `let`/`pick` branches in
  `eval_keyword_expression`).
- **`f()` (zero-argument call) doesn't parse** ("why not `f()`???") —
  confirmed: `arity f 1` (or any arity/bracket combo) followed by `f()`
  raises `SyntaxError: token \`)\` cannot start an expression`, because
  brackets' `nud` (line 1137) unconditionally tries to `parse_expression`
  before expecting the closing bracket — there's no path for "immediately
  see the closing bracket". Fixing this means special-casing an empty
  bracket body in `add_brackets`'s `nud`, and deciding what `f()` should
  even parse *to* (a 0-arg application node, distinct from bare `f`).
  Self-contained but touches core parsing; worth a design decision first
  (see `suggestions-claude.md`).
- **"do checks for `case` statements"** — confirmed: `case` is handled
  completely identically to `assume` everywhere (`eval_keyword_expression`'s
  combined `assume`/`case` branch, line 2700, and `eval_done`'s combined
  `'assume' | 'case'` branch, line 2032) — there is no case-specific
  validation (e.g. that the cases are exhaustive, or that the case
  expressions are mutually related to a disjunction already in scope before
  `or-elim` fires at the end). Small, localized addition once it's decided
  what "check" should mean.
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
- **`save` command** ("have a `save` command that stores the current theory
  and state") — feasible with existing machinery: `KnowledgeBase` already
  has `theory_str()`, `syntax_str_all_levels()`, etc. for printing
  everything back out; a `save "file.kurt"` keyword could just redirect
  those same printers to a file, in a form that re-parses via `load`. The
  open design question is exactly what "state" means (just the theory? also
  syntax declarations made ad hoc in the session? the level stack, which
  can't sensibly round-trip through a flat file?).
- **`sandbox` can now discard by dedenting too (not just `break`), but still
  never commits** ("have a `sandbox` block, where we first try and try, and
  then store it to the theory") — the file/shell unification (see
  `doc/kurt-doc.md` §9) made `sandbox` close by plain dedent, discarding its
  contents exactly like `break` does; what's still missing is any way to
  *keep* what happened inside instead. Adding that (e.g. a distinct closing
  keyword, or merging on `qed` the way a `proof` does) remains a bounded,
  well-scoped feature — just no longer blocked on `sandbox` being
  shell-only, since it isn't anymore.
- **Chains don't generate real transitivity** ("`chain`s are always
  transitive"; "for `a=b≠c=d`... if it is transitive also more") —
  confirmed by reading `get_chain_op`/`check_with_other_chains` (line
  910-953): `chain` only affects *parsing* — it decides which operator a
  continuation line desugars to (picking the "strongest" operator seen so
  far in one written chain). It does not add any general transitivity
  *inference* rule usable outside of one hand-written chained proof step.
  Making declared chains genuinely transitive (so `derive_expr` could
  combine `a R b` and `b R c` into `a R c` for any declared chain `R`,
  the way `impl_elim` already combines separately-proven facts) is real,
  scoped work inside `derive_expr`, though it interacts with the perf
  concerns below (more candidate matches to try per step).
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
- **`nonassoc` operators** ("implement 'nonassoc', this could then be
  checked in 'post_process'") — `add_infix` currently always resolves
  associativity from `lbp`/`rbp` (confirmed via `parse_expression` and the
  binding-power comparisons); there's no way to declare e.g. `<` as
  non-associative so that `a < b < c` is a syntax error rather than silently
  parsing one way or another. Well-scoped: a new `infix ... nonassoc` form
  (or a separate `nonassoc` keyword as titled) plus a check in
  `post_process` (line 1876) or the parser itself.
- **`'thus'` keyword** ("'thus' with one step shorter, for `qed` we use
  match, for `thus` we use equal") — not implemented at all today (no
  `'thus'` anywhere in `eval_keyword_expression`'s dispatch). The todo's own
  description is a usable spec: unlike `qed`, which re-derives the planned
  goal via full `derive_expr` search, `thus` would close a block (or end an
  equational step) by checking the last formula is *literally equal* (via
  `equal_expr`, already used elsewhere for exactly this kind of check) to
  the target, which is cheaper and more predictable for long equational
  chains (see `group.kurt`'s style of proof). Well-specified, self-contained
  new keyword.
- **`Formula.origin`** ("have `origin` (see class Token) also on the
  Formula level") — `Token` (line 331) already carries an `origin` field;
  `Formula` (line 369) does not. Small, mechanical addition, useful for
  provenance/debugging (e.g. "which `load`ed file did this axiom really
  come from" beyond just `filename`/`line`).
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

## Needs investigation before it's clear what "feasible" even means

- **"why (not x in emptyset) not working?"** — I reproduced the ingredients
  (`set.kurt`'s `def ∅ = { $a | false }`) but did not reproduce a concrete
  failing proof from the one-line description alone; needs the maintainer's
  original failing snippet to make progress.
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
- **"allow multiple replacement in one step (is that possible?)"** — the
  maintainer's own phrasing suggests this is genuinely open; `
  generate_all_combinations`'s comment explicitly says "allow only one
  subterm to be replaced, much more efficient" as a deliberate simplification.
  Needs a concrete motivating example (a proof that actually needs
  multi-site substitution in one step) before it's clear whether it's
  worth the complexity.
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

## Deliberately left out (too broad / not really a `kurt.py` task)

Vague/philosophical items ("check theories", "make a good verbose mode for
teaching"), pure research directions ("two algorithms: constraint-based vs
substitution-based (W)"), external/infra projects (running under Pyodide,
VS Code / LSP integration — both plausible but each a separate project, not
a `kurt.py` change), and inspirational links (the Terry Tao Lean posts, the
Haskell indentation wiki page) are intentionally not listed above as
"feasible tasks" — see `suggestions-claude.md` for the ones worth carrying
forward as longer-term ideas.
