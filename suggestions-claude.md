# suggestions-claude.md

Ideas for Kurt's language and implementation, from reading `src/kurt/kurt.py`
end to end (lexer through CLI) and from writing the `tutorial/` lessons.
These are my own suggestions, not drawn from `todo.md` — see
`todo-claude.md` for the filtered, verified pass over the existing backlog.
Grouped by theme, roughly most- to least-impactful given Kurt's stated
purpose (immediate, automatic feedback for students learning to write
proofs). No code was changed while writing this.

## Pedagogy and error-message quality

This is the area I'd invest in first — Kurt's whole reason for existing is
giving students fast, useful feedback, and today's error messages are
accurate but terse (`ProofError: can not derive \`A\``), which tells a
confused student *that* they're wrong but not *why*, or what's close.

- **"Did you mean...?" for failed derivations.** When `derive_expr` fails,
  Kurt already has, right there in `kb.all_theory()`, every axiom and
  proven fact in scope. Before giving up, it could look for the
  *closest* formula (same top-level operator, right arity, one mismatched
  argument, or a plausible `sym`/argument-order swap) and mention it:
  `can not derive \`A or B\` -- did you mean \`B or A\`? \`or\` is symmetric,
  but the formula in scope is \`A and B\`` (say). Even a much cruder version
  — "the closest axiom by top-level operator is X" — would turn a dead end
  into a nudge in the right direction, which is exactly what a human tutor
  would say.
- **Give the inert `hint` keyword a real job that fits this.** Right now
  `hint`/`hint on` (see `todo-claude.md`) toggles a flag nothing reads.
  Rather than a generic "hint before every prompt" (vague, per `todo.md`'s
  own phrasing), a concrete, scoped version: when `hint on`, a *failed*
  `show`/derivation prints the closest-candidate suggestion above, and a
  block that's still open prints what keyword would close it and what rule
  that triggers (`"...you're inside an \`assume A\` block; closing it now
  would give you \`A implies <whatever you just proved>\`"`). That's
  something `KnowledgeBase` already knows (`kb.mode_str`, `kb.mode_args`) —
  it's a presentation problem, not a new inference engine.
- **A `--report`/JSON diagnostics mode for grading.** Kurt's own docs call
  out the autograder use case explicitly (CLAUDE.md: "designed for students
  to get immediate feedback, similar to automated testing"). Every
  `KurtException` already carries `line`/`column`/`filename`; every
  `Formula` carries its `line`/`reason`. A `kurt --report json file.kurt`
  mode that emits one JSON object per checked line (`{line, formula,
  status: proven|axiom|todo|error, reason}`) plus a final summary would let
  an instructor grade a folder of submissions programmatically today,
  without inventing anything Kurt doesn't already track internally.
  Combined with the exit-code fix in `todo-claude.md`, this turns Kurt into
  a real CI-friendly tool, not just an interactive REPL.
- **Treat "Proof almost checked: N todos" as a partial-credit score.** It
  already exists (`main()`, the `todos()` count) — formalizing it (e.g. a
  `--score` flag that prints `checked_lines / total_lines` or `1 -
  n_todos/n_claims`) is a small step from what's already computed, and
  turns every `todo`-riddled skeleton proof into an auto-gradable
  assignment along a spectrum, not just pass/fail.
- **~~An in-language "this should fail" construct~~ — done, as `expect`.**
  (Named `expect` rather than `expect-error`: Kurt identifiers can't contain
  a hyphen — `[$%@]?[A-Za-z][A-Za-z0-9]*` — so `expect-error` would have
  lexed as three separate tokens.) See `doc/kurt-doc.md` §9.6 and
  `tutorial/15-expect.kurt`. It checks `KurtException.kind`, not message
  text, so it doesn't share the old marker convention's fragility. One
  real, documented limitation surfaced during implementation: the block
  can't itself open a nested block (`show`/`proof`/`assume`/etc.) — the
  simplest robust version only catches an error raised *directly* inside
  it, at the same level; a version that also caught errors from a nested
  sub-block turned out to need either a careful multi-level unwind past
  `pop_level()`'s own validation (which itself raises on an abandoned,
  unresolved `show`) or an ancestor-search that risks getting the
  in-progress lexer indentation bookkeeping out of sync — not worth the
  risk for what the tutorial/test retrofits actually needed.

## Small, high-leverage usability fixes

- **Run LaTeX-command input replacement on files, not just the REPL.**
  `replace_latex_syntax` (line 248) already turns `\forall`, `\exists`,
  `\alpha`, `\leq`, etc. into their Unicode glyphs — but `read_eval_loop`
  only calls it in the interactive branch (`if not is_file:`), never when
  reading a `.kurt` file. That means a student without an easy way to type
  `∀`/`∃`/`≤`/Greek letters (most keyboards) can use them fluently at the
  prompt but not in a saved proof file, which is backwards for a classroom
  tool where files matter more than one-off REPL sessions. Turning this on
  for files too (and documenting it — I found this by reading source, not
  from any doc) seems like a quick, high-value win. Worth deciding whether
  it should be unconditional or opt-in (some theory might one day want a
  backslash-prefixed operator of its own, though none currently exist).
- **A `kurt --format` / pretty-printer mode.** `expr_normal`/`expr_sexpr`
  (lines 1462-1501) already know how to render any expression consistently
  given the current `KnowledgeBase`'s syntax table. A `kurt --format
  file.kurt` that rewrites a proof file into a canonical layout (consistent
  spacing around operators, consistent indentation) would be a small
  wrapper around printers that already exist, and would help keep a
  classroom's worth of submitted `.kurt` files visually consistent (the way
  `black`/`gofmt` do for their languages) — plausibly useful for anyone
  grading by eye as well as by script.
- **Surface the live syntax table as a syntax-highlighting grammar.** Kurt's
  grammar is unusually self-describing: at any point, `kb.syntax_str_all_levels()`
  (already used by the `syntax` keyword) can enumerate every declared
  infix/prefix/postfix/bindop/bracket operator with its binding power. A
  small script that dumps a *given theory's* operator table (e.g. after
  `load logic`) as a TextMate grammar or tree-sitter query would give editor
  syntax highlighting almost for free, and is a much smaller lift than the
  full VS Code/LSP integration `todo.md` mentions — a good first milestone
  toward it, usable even before an LSP exists.
- **An "unused axiom" lint.** Every `use`d axiom is a `Formula` sitting in
  `kb.theory`; every successful derivation step records which formulas it
  used (the `reason` strings, e.g. `by 3, 2`). A post-hoc pass that checks
  whether every `use`d formula was ever referenced by a later step could
  flag "you assumed `B` but never needed it" — a very common thing for a
  student to want to know ("did I over-assume?"), and the bookkeeping
  (`Formula`, `formula_ref`) to build it already exists; it would mostly be
  a new pass over the accumulated `reason` strings/references rather than
  new inference machinery.

## Language features

- **Let `sandbox` optionally "graft" its result, not just discard.**
  Complements `todo-claude.md`'s note that `sandbox` still only ever
  discards (whether closed by dedenting or by `break`). The natural
  pairing: keep `sandbox`/dedent/`break` for pure scratch work (today's
  behaviour), plus a `qed`-like "commit" close for the "let me try this
  derivation and keep it if it works" workflow the todo item describes.
  This also gives an editor-driven session a much better "try before you
  commit" loop than opening a whole `show`/`proof` block for something
  exploratory.
- **A `why`/`explain` keyword for the last (or a given) step.** Right now
  `verbose` prints extra detail *while* a match happens; there's no way to
  ask *after the fact* "why did line 7 work?" beyond scrolling back to the
  original log line's `reason`. A `why 7` (or `why` for the last line) that
  re-explains a specific proven formula — which axiom/rule fired, what
  substitution was used — would be useful standalone (revisiting an old
  proof) and as the foundation for any future visual proof-tree tool.
- **A user-extensible `avoid PATTERN, ...` keyword, to add more warning
  shapes beyond the hardcoded ones in `bare_bool_schema_axiom_warning`.**
  Discussed and not pursued — the actual danger condition ("does this schema
  variable fail to reappear elsewhere in the formula") is a
  negative-occurrence check, not an ordinary structural pattern match; even
  wildcard notation (`avoid %A iff _, _ iff %A`) doesn't sidestep this
  unless `_` specifically means "anything not containing the other named
  variable", which is the same primitive wearing different syntax. Would
  need a genuine new Kurt-level primitive (exposing something like the
  internal `contains`/`State.occurs` helpers), not a small extension of the
  existing pattern-matcher. Full writeup in `doc/kurt-soundness.md` §6.
- **Generalize `chain` beyond parsing sugar into real transitive reasoning**
  (elaborated with more implementation detail in `todo-claude.md`) — I'm
  repeating it here because it's the single feature gap most likely to
  surprise a mathematically-minded user: writing `a = b`, `b < c` and
  expecting `a < c` "for free" the way a chain's *syntax* already implies
  is a very natural expectation for anyone who has written `a = b < c` on
  paper, and today it silently requires an extra manual proof step per
  chain use.
- **A documented, first-class way to declare a theory's dependencies as
  metadata, not just `load` side effects.** Theories already `load` their
  own prerequisites (confirmed: `equality.kurt` loads `prop`, `set.kurt`
  loads `equality, logic`, etc.) — the one thing missing is any way to ask
  "what does theory X depend on?" without opening the file and reading its
  `load` lines, or to detect at a glance that, say, `lambda-calculus.kurt`
  currently declares no dependencies at all (worth double-checking it's
  truly self-contained). A `kurt --deps
  theory.kurt` that just walks `load` statements recursively and prints the
  tree would make the theory ecosystem's structure visible instead of
  implicit.
- **A small "theories registry" convention for third-party packages.**
  `-p`/`--path` and `theory_path` already generalize where `load` looks
  (cwd, then packaged theories, then a user path) — the missing piece for
  a growing community of theory authors (once this is public) is a
  lightweight convention for naming/versioning a theory package (even just
  "one `.kurt` file per Git repo, discovered via `-p`", documented as the
  supported extension point) so instructors can share domain-specific
  theories (a specific course's axioms, say) without vendoring them into
  this repo.

## Architecture

- **Consider a plugin-style output-renderer abstraction instead of a global
  `latex_flag` + `kb.format`.** Right now `log()` (line 2960) branches on a
  module-level `latex_flag` global and `kb.format`, and `main()` mutates
  more globals (`debug_flag`, `comment_indent`) directly. This works for
  "print to stdout, optionally as LaTeX", but it's the kind of thing that
  gets awkward the moment there's a second consumer of Kurt's output (a
  future browser playground, an editor extension, a JSON reporter per the
  suggestion above) that wants structured events rather than pre-formatted
  strings printed straight to `sys.stdout`. Emitting a stream of small
  structured records (`{kind: 'formula'|'error'|'log', ...}`) from the core
  evaluator, with formatting (`normal`/`sexpr`/`latex`/`json`) as a
  presentation layer on top, would decouple "Kurt checks a proof" from
  "Kurt prints to a terminal" — which is also exactly what the Pyodide/
  browser idea in `todo.md` will eventually need anyway (a browser
  playground can't `print()` to a real stdout).
- **`KnowledgeBase` is doing a lot** (syntax tables, the theory, the level
  stack, mode/toggle flags, todos, loaded-files bookkeeping — the class
  spans lines 587-1447, ~860 lines). None of it looks wrong, but a few of
  these are genuinely orthogonal concerns bolted onto one object (e.g. the
  `format`/`verbose`/`hint`/`calc` toggles vs. the actual proof
  state). Splitting "session settings" (toggles, format) out from "proof
  state" (theory, levels) would make it easier to reason about what
  `push_level`/`pop_level`/`merge_and_pop` are actually supposed to copy vs.
  share vs. reset — right now that's implicit in which fields happen to
  read `parent.X` as a default (line 588 onward) and which don't, and it's
  easy to imagine a future toggle being added without noticing it needs the
  same "always read from the root" treatment `format`'s setter gives it
  explicitly (line 2220, the `while kb.parent is not None` loop —
  `hint`/`verbose`/`calc` don't do this, so toggling them inside a
  nested block vs. at the root may behave inconsistently; worth a
  deliberate check either way, whatever the intended semantics are).
- **The multiset-style matching for flat+symmetric operators deserves to be
  documented as a feature, not just an implementation detail.** Reading
  `symmetrize_all`/`flatten_op`/`canonical_key`/`sort_exprs` (lines 1746-
  1809), a flat *and* symmetric operator like `and` gets its arguments
  canonically sorted before matching, which means Kurt is effectively doing
  *multiset* matching for conjunctions (`A and B and C` matches a stored
  `C and A and B` without needing `sym` to be invoked argument-pair by
  argument-pair). That's a genuinely nice property — worth a paragraph in
  `doc/kurt-doc.md` and maybe a tutorial aside, since right now a reader has
  to infer it from the sort/canonicalization code rather than being told.

## Smaller ideas noticed in passing

- `is_var`/`is_const` recursion up the parent chain (lines 888, 903) is
  simple and correct today, but it's another place that will need
  revisiting together with the "file-local variables" design work in
  `todo-claude.md` — worth doing both at once rather than separately.
- `new_var_name`/`new_bool_var_name` use a Python function attribute
  (`new_var_name.counter`) as global mutable state across the whole
  process — harmless today, but it means two completely unrelated proofs
  checked in the same process (e.g. two files in one `unittest` run, or two
  `load`s in one REPL session) get fresh-variable names that depend on
  *how many* fresh variables any earlier, unrelated proof needed. That's
  almost certainly fine semantically (the names are meant to be opaque), but
  it does mean error messages that mention a generated name (like
  `forall-elim-fail.kurt`'s `$$var552`, see `todo-claude.md`) are
  order-dependent across a whole test run, not just file-local — another
  reason those exact-name-in-error-message tests are fragile.
- **~~Warn when a `use` axiom is (or reduces to) a bare `%`/`$`-prefixed
  variable~~ — done.** Found while investigating the mixed-boolean-`let`
  question in `doc/kurt-soundness.md` §6: `use %A` alone makes *every*
  boolean proposition immediately derivable, and `use %A implies P` makes
  `P` immediately derivable — both are logically correct consequences of
  what such an axiom actually asserts ("for any proposition `%A`, `%A`
  holds" is self-evidently false, and anything follows from a false
  premise), but it's an easy trap for a theory author to fall into by
  accident (e.g. meaning `%A` as "some specific, unstated proposition"
  rather than "every proposition"). Implemented as a **warning, not an
  error** (printed to stderr, from `bare_bool_schema_axiom_warning`, called
  from `eval_use` so it also covers `def`) — it only pattern-matches the
  handful of obvious shapes (bare `%A`; `%A implies X`/`d iff %A` where the
  variable doesn't reappear on the other side), not every equivalent
  phrasing, since that would need deciding in general whether an arbitrary
  formula is a tautology. See `doc/kurt-soundness.md` §6,
  `doc/kurt-doc.md` §6.2, and `tests/test_bare_bool_schema_warning.py`.
