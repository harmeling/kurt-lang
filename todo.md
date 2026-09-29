# TODOs

git checkout main && git pull && git merge dev && git push && git checkout dev

## proofs-not-yet (postponed, analysed 2026-09-25)

- TODO `scalar-product.kurt`: `brackets < >` clashes with the relation `<`, and the lexer rejects `⟨ ⟩` -- decide: allow `⟨ ⟩` in the lexer, or write `ip a b`.  fix the math (`λ = <a,b>/<b,b>`, case `b = 0` separately), add `<a,a> ≥ 0` and bilinearity for `-`.  vectors share `+`/`*` with numbers (see namespaces below), or use separate symbols like `⊕`
- DONE `limits.kurt`: now `proofs/analysis/limit-of-linear-function.kurt`, with `analysis.kurt` and the rules for conditions in `logic.kurt` (2026-09-28)
- TODO `pick` for an `∃` with a condition: currently via "exists-cond-def" first (`∃ $y ($y > 0 ∧ ...)`), then `pick`
- TODO `argmax`/`argmin` in `analysis.kurt`: not unique, so not `argmax ... = $a`; "some maximizer" needs `sub` with an `argmax` term as value, which is nested `sub`
- DONE `calc` while matching a rule, for parts whose variables have values (2026-09-29); not done: solving, e.g. `$b / 3` against `0` with `$b` unknown (from "gt-div-pos"), or `1! = 1` from `1! = 1 * 0!` and `0! = 1` in one step (the search works backwards from the goal)
- TODO `square-root-two-is-irrational.kurt`: reducing `m/n` to lowest terms is a hidden induction -- decide: well-ordering axiom in `natural.kurt`, or "every rational has a coprime representation" as an axiom of `Q`.  needs a theory of `divides`/even/odd with the lemma `2 divides m*m ⇒ 2 divides m`; rewrite `exists (m, n)` as `exists m exists n`, `begin`/`end` as `case`, `:=` as `def`, `contradiction` as `false`

## postponed from the tutorial discussion (2026-09-26)

- DONE `save` as a replay of the accepted input lines instead of a flattened snapshot (2026-09-29; still allowed in files, it writes their lines so far)
- TODO shell: pre-fill each input line with the current indentation (readline `set_startup_hook`), so that a backspace dedents
- TODO `use` only *directly* in a `sandbox`/`expect`, not in a proof block nested inside them (two soundness tests need `use P $w` before the block instead)
- TODO get rid of the `;;; ` markers: `expect` with an optional message prefix, and file-level errors (EOF, unclosed blocks, `break` at top level) via `expect` around a `load` of a helper file in a directory the test discovery skips
- DONE `f(a,b)` for a function of arity 2 means `f a b` (2026-09-29), where the function wouldn't get enough arguments otherwise
- TODO minimal core: remove the name-based special cases (`iff`, `not`/`false`, `=`/`iff` for `def`) so that `minimal.kurt` really is the core -- the core is first-order natural deduction (`implies`, `and`, `forall`, `sub`, bool vs. non-bool), not a logic-neutral framework
- TODO quantifiers only with `load logic`: `forall`/`exists` syntax and the blocks `let`/`pick` become available only then (smaller core for propositional/modal courses); the engine's by-name handling of `forall` (e.g. stripping outer quantifiers of facts) must then depend on it being declared
- TODO modal necessitation ("from a theorem A infer □A") can't be written: `use %p ⇒ □%p` would be unsound. A small `rule %p / □%p "nec"` for rules that only apply to theorems (facts proven with no assumption open) would do

- DONE (2026-09-29) a loaded file is checked in the context of what was loaded before it: its proofs see (and could use) facts it doesn't load itself, and get slower with every theory around (group.kurt: 3 s alone, 8.5 s after `load arith`). Load a file in a fresh context instead (only what it loads itself), then add its exports?

## on the way to 0.9 and 1.0 (2026-09-29, see release-plan.md)

before 0.9 (public):
- DONE a targeted soundness review of what the kernel doesn't check independently: the block rules, `def`, `load`/exports, `calc`, the normal forms (`flat`, `sym`) -- four bug hunts, all found bugs fixed with regression tests (doc/kurt-soundness.md §8.17, 2026-09-29)
- TODO what the soundness review left open: curried `(f x) y` and `f x y` are two different terms; a sum whose bound variable shadows an outer one (`sum x (0, n) (sum x (0, x) x)`) isn't derived by "sum-last"; the reasons of trivial steps name unrelated rules (`a = a` "by chain-trans-0-0(pow-identity, pow-identity)"); an error shows the internal bracket node as `()`; `chain R` in a block names a pseudo-file `<chain transitivity ...>`; a chain can't continue the line that opens a block (`assume a < b` / `    = c`) -- only an error now
- DONE (2026-09-29) loading in a fresh context (see below): a library's proofs must not depend on what its loader loaded before -- on top of the `ExportBundle`, with a cache by path and hashes (codex-suggestions.md, P0)
- TODO public polish: README, version number, the internal files in the repo root, PyPI
- TODO docs for the new features: `cert`, `.kurtc`, tuples, groups, operator variables in the tutorial (the cookbook has 20 recipes now, by Codex, 2026-09-29)
- DONE (codex-suggestions.md, P2, 2026-09-29) three small bugs: `parse` never prints `type check failed` (`keyword_token in ['parse']` compares a `Token`); a `def` line with several definitions logs the last one for each; REPL history is written but never read (`and False` in `main`)
- DONE (2026-09-29) (codex-suggestions.md, P0) `merge_and_pop` merges by looping over `__dict__` with an exclusion list (which has the typo `mode_expr` for `mode_args`): a new field is exported by default -- replace by an explicit `ExportBundle` (compute, validate, apply), fail closed
- TODO (codex-suggestions.md, P2) consistency pass before 0.9: line and test counts in CLAUDE.md and release-plan.md (better generated or dated), release-plan.md still says "the whole matcher is trusted" next to the kernel, set.kurt's opening comment promises function extensionality, the empty file `kurt` in the repo root, no `src/kurt/__main__.py` (`python -m kurt`), build and install sdist/wheel in CI

before 1.0:
- TODO (codex-suggestions.md, P0 for 1.0) reduce the kernel's trusted base: its own alpha-equivalence and binder reading (not `equal_expr`/`unpack_condition` of the search -- the review of 2026-09-29 found a misreading both shared), an immutable environment, a test that kernel code doesn't call search code, and say for `flat`/`sym`/`calc` whether they are checked steps or trusted semantics
- TODO (codex-suggestions.md, P1) a per-run context instead of module globals (`strict_mode`, counters, `certificates_by_line`, ...) and a small API (`check_text`, `check_file`), with the CLI on top -- for the browser, editors, graders
- TODO (codex-suggestions.md, P1) index the theory by top-level operator for the search, with benchmarks first; keep the order of the theory, so reasons don't change
- TODO (codex-suggestions.md, P1) structured events (accepted, failed, block opened/closed, ...) and the text output as one renderer of them; JSON for graders; `why`/hints from certificates
- TODO freeze the language (release-plan.md: minimal core, labels, `use` in nested sandboxes, ParseError vs. EvalError, the kernel's dependency rule)
- TODO scalars vs. vectors (decides the structure of arith.kurt, see below)
- TODO a semester of use with students
- TODO exact vector operations for the calculator, shipped with Kurt (componentwise add, scalar multiplication, scalar product on tuples), instead of theories with their own calculators -- a calculator from a theory file would be trusted code from anywhere, and numpy is not exact

## open points from the discussion of 2026-09-29

- TODO a `todo` inside an `expect` or `sandbox` still counts as an open `todo` of the file, although the block is discarded
- TODO `unpack_condition` reads a condition's bound variable from which symbols are constants, not from the enclosing binders -- a guard in `eval_done` catches where that changes when a block closes; better: read it with the enclosing binders, or store the bound variable with the condition

- TODO mappings as sets of pairs (with their domain), so that function extensionality holds -- removed from set.kurt on 2026-09-29, since it was false for mappings as opaque objects (every object is in `∅ → B`, which gave `0 = 1`)

- TODO scalars vs. vectors: arith.kurt's laws hold for *everything* written with `+`, `*` -- so vectors can share `+` with numbers only if (a) arith's laws get the condition `$a ∈ R` (every arithmetic proof then needs membership facts: numerals automatically? `let x ∈ R`?), or (b) arith becomes an instance of a structure, like group.kurt: `field(R, (+), (*), 0, 1, (-), inv)`, and vectors `vector-space(V, R, ...)`. Try (b) with rings/fields first?
- TODO the inner product: after scalars vs. vectors; `⟨ ⟩` can be declared per file (`brackets ⟨ ⟩`), proofs-not-yet/scalar-product.kurt (Cauchy-Schwarz) waits for it. Not done: `bra`/`ket` as words for `⟨ ⟩` (only the shell shortcuts `\langle`, `\rangle`)
- TODO group.kurt with a `flat` operator: a pattern `$a ∘ $b` matches `x + y`, but not `x + y + z` (one term with three arguments) -- fine for `+`, whose associativity is built in, but proofs for `+` and for an abstract `∘` look slightly different
- DONE `calc`: theories bind their symbols to the built-in calculator (`calc + add, ...`), exact numbers (`Fraction`) (2026-09-29)
- TODO `calc` for predicates: e.g. `calc ∈ Nat is-natural`, so that `3 ∈ Nat` follows by `calc`
- TODO own calculators for a theory (e.g. numpy for vectors)? see the discussion of 2026-09-29: only as exact, trusted code shipped with Kurt, not from a theory file
- TODO `calc` doesn't solve: `$b / 3` against `0` with `$b` unknown, or `1! = 1` from `1! = 1 * 0!` and `0! = 1` in one step (the search works backwards from the goal)
- TODO printing: a comma list in custom brackets shows as `⟨ (a , b) ⟩`; a negative literal as `-8 ^ 0.5`, which reads as `-(8 ^ 0.5)`
- TODO `def` by pattern matching on constructors (`def fact 0 = 1`, `def fact (s $n) = (s $n) * fact $n`) -- currently the left-hand side must be the new symbol applied to distinct variables, so recursive definitions go through `use`. Safe if: (1) only declared constructors in patterns (`constructors Nat 0, s`, distinct and injective by the theory), never `+`, `*` (`def f ($x + $y) = $x` gives `f 3 = 1` and `f 3 = 0`); (2) the patterns of one symbol don't overlap; (3) structural recursion only (`def f (s $n) = f (s $n) + 1` gives `0 = 1`); (4) all equations of a symbol form one definition, the symbol new at the first one. Not exhaustive is harmless (the value stays unknown)
- TODO the kernel's rule for when a schema variable may depend on a bound variable: implicit as now, declared (Isabelle's `?T i`), or Metamath-style distinct-variable conditions (release-plan.md)

## NEXT

- TODO solve the path puzzle, also check `load ../foo.kurt` whether it works
- TODO add `(%A iff top) implies A` to `prop.kurt` and check some mafi1 example
- TODO allow `let x with F(x)`, or `let F(x)`, or `let x>0`, merge `pick` and `let` to use `unpack_condition`
- TODO automatically iterate over all implications, in particular convert `≡` into two implications
- TODO why (not x in emptyset) not working?

- TODO write the tutorial
- TODO verbose mode should give context dependent hints before each prompt, `hint`
- TODO iterate over the formulas in theory and over all conclusions (RHS of implications) as well
- TODO make a good verbose mode for teaching/being helpful
- TODO better inference rules that should make part of `impl_elim` not necessary: when iterating through `all_theory()` also iterate over RHS of implications where the LHS is part of the theory
- TODO `chain`s are always transitive
- TODO dependencies: who loads what?  a theory should load all necessary stuff, let theories load their own dependencies
- TODO check that in forall_intro the quantification either applies to boolean or non-boolean vars, but not both
- TODO repairs messages for 'pick', 'fix', 'assume'
- TODO check  if lbp > rbp then left-assoc else right-assoc
- TODO check theories
- TODO check again what rules are hard-coded
- TODO think about short-cut by equality-elim, just compare last two expressions and find the difference, then search for the corresponding equation, this should be much faster
- TODO check conditions in `logic.kurt`

## TOPICS before releasing 1.0

- TODO binding of SPACE for `sum` vs `forall`.  can we have different values?
- TODO make the Expr objects also frozen, create also some class for it
- TODO do checks for `case` statements
- TODO don't create all those Tokens on-the-fly, but some like the `not_token` can be created and reused.
- TODO get rid of labels, just make the first word of the comment after a formula its label, get rid of string data type
- TODO space binding: for quantifier it should be higher, for limits, sums higher
- TODO maybe the code gets simpler, when self.used and self.bool gets merged.  i.e., all used symbols have a type!
- TODO have a `save` command that stores the current theory and state
- TODO have a `sandbox` block, where we first try and try, and then store it to the theory
- TODO get group.kurt working with constants and with `var x, y, z`
- TODO do calculations with integers and reals
- TODO what should go into `minimal.kurt`?  what into `propositional.kurt` and `logic.kurt`?
- TODO define what get's exported when loading a file, make variables declarations local?
- TODO get coverage of 100% in the unit tests
- TODO test the conditions for forall and exist rules
- TODO what should be loaded by default?  `minimal.kurt` or `standards.kurt`?
- TODO check all KurtExceptions for ProofError, ParseError, SyntaxError, EvalError
- TODO check the inference for quantifiers, whether there must be more restrictions, or does the renaming handle it?  try to violate them
- TODO local and export features, files should open a new level, but can export statements as axioms ('use') to the level above them
- TODO write documentation/tutorial for the language
- TODO refactoring: work through all 'mainstream', can we avoid them?  check also `decorate_reason` and `formula_ref`.  yes, store the reason in the formula, then generate a log string later up, but we don't need the `mainstream` flag anymore, possibly we need it since some impl-elim are also generating logs, similarly, remove the 'filenames' that are passed around
- TODO search all TODO in the code and check whether they are still relevant
- TODO when should the calculation happen?  only for simplified expressions?  have a flag?

## TOPICS before releasing 2.0

- TODO do the parsing for the syntactic stuff already in the lexer (see rule for `load`), i.e., the comma processing
- TODO should substitutions be always boolean (see `type_check_expression`)
- TODO variables and syntax should be file only, i.e., the `theory` is exported, but the syntax is not.  problem: how to show formulas that are imported (just as quotes?  e.g. `[equality.kurt] %a and %b implies %b and %a`
- TODO add column information for the exceptions, use `expr_column`
- TODO instead of brute-force matching, use more clever matching, e.g., search for the sub terms, or have a dictionary of all subterms
- TODO let it run locally in the browser, e.g., using Pyodide <https://pyodide.org/en/stable/>, see <https://chatgpt.com/share/68387cb6-7df4-8008-af44-da04c4449f10>
- TODO namespaces, e.g., for scalar-product.kurt, see `kurt-notes.md`, search for `namespace`

## TOPICS for the future

- TODO macros: `macro ($A // $x=$a) (sub $x $a $A)` expands during parsing
- TODO run profiling
- TODO other ideas for speedup:
  1. Add memoization or caching to deepcopy_expr() if there are repeated shared subtrees.
  2. Use a tree fingerprint or identity system to detect when actual cloning is needed.
- TODO `find sub $x $a forall $z $A`, does this one work?  where the formula for the substitution is nested
- TODO put lots of negative proof examples in to `tests/proofs` as well
- TODO allow boolean expressions for the bound variable for some variable binding operators
- TODO allow commandline args for setting builtin keywords, such as `implies` and `and` and `=` and `sub`
- TODO CHECK THE IMPLEMENTATION WHETHER CONSTRAINTS (i) and (ii) for bindop are enforced
- TODO check whether we need a version of `equal_expr` that allows bounded renaming
- TODO check number of possible variable names, use letters to be safe
- TODO `def ($A // $x=$a) = sub $x $a $A` as a macro mechanism, i.e., just syntactically instead of `use`
- TODO type checking for `sub $x $a $A` with free and bound variable check
- TODO have `origin` (see class Token) also on the Formula level
- TODO substitutions are only allowed in `use` lines, not in regular stuff, so they are designed to formulate axiom schemata.
- TODO check that `minimal.kurt` is really hard-coded here
- TODO matching set of formulas: first match the ones without substitutions, then the ones with (can we detect, when it doesn't work?)
- TODO create an initial version and start working on the branch
- TODO maybe it is a good idea to always have variables with $x and constants without them.  However, using `$+` might be cumbersome.  So having the ability to write `var (+)` might be useful.
- TODO runtime; currently: `derive_expr` is O(n^k) where n is the length of the theory and k is the maximum number of premises of an proved implication,
-      this could be speed up with better data structure to store the formulas of the theory, but let's first keep it slow, but understandable
- TODO allow outer forall block around implications
- TODO write kurt integration for vscode, highlight the lines that are proven, <https://microsoft.github.io/language-server-protocol/>
- TODO two algorithms: constraint based (<https://www.youtube.com/watch?v=H7x4THVU4BQ>) and substitution based (W)
- TODO redo something like
  <https://terrytao.wordpress.com/2023/12/05/a-slightly-longer-lean-4-proof-tour/>
  <https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/>
- TODO organize the implications as a dictionary of lists with the top-level operator of RHS as the key
- TODO implement 'nonassoc', this could then be checked in 'post_process'
- TODO integration:    `int x in (0, 1)  f(x)
- TODO replace `functool.cmp_to_key` and rewrite `compare_expr`
- TODO LBYL and EAFP Coding Style? <https://realpython.com/python-lbyl-vs-eafp/>
- TODO <https://en.wikibooks.org/wiki/Haskell/Indentation#:~:text=The%20golden%20rule%20of%20indentation&text=When%20you%20start%20the%20expression,acceptable%20and%20may%20be%20clearer).&text=This%20tends%20to%20trip%20up,expressions%20must%20be%20exactly%20aligned.>
- TODO use the Token.column information
- TODO add syntactic sugar for case distinctions
