# TODOs

git checkout main && git pull && git merge dev && git push && git checkout dev

## proofs-not-yet (postponed, analysed 2026-09-25)

- TODO `scalar-product.kurt`: `brackets < >` clashes with the relation `<`, and the lexer rejects `⟨ ⟩` -- decide: allow `⟨ ⟩` in the lexer, or write `ip a b`.  fix the math (`λ = <a,b>/<b,b>`, case `b = 0` separately), add `<a,a> ≥ 0` and bilinearity for `-`.  vectors share `+`/`*` with numbers (see namespaces below), or use separate symbols like `⊕`
- TODO `limits.kurt`: `∀ε>0` must be written `∀ ($e > 0)` since `>` binds weaker than space -- decide whether relations should bind tighter than function application.  missing: exists-intro for a conditioned `∃` (from `c > 0` and `P c` derive `∃ ($d > 0) (P $d)`), `abs` instead of `|x|` (`|` is taken by set comprehension) with its laws, fix `load forall`/`load arithmetics`, drop the notes in lines 22-36
- TODO `square-root-two-is-irrational.kurt`: reducing `m/n` to lowest terms is a hidden induction -- decide: well-ordering axiom in `natural.kurt`, or "every rational has a coprime representation" as an axiom of `Q`.  needs a theory of `divides`/even/odd with the lemma `2 divides m*m ⇒ 2 divides m`; rewrite `exists (m, n)` as `exists m exists n`, `begin`/`end` as `case`, `:=` as `def`, `contradiction` as `false`
- TODO sums with an arbitrary summand: a non-boolean `$T` in `sum $i ($a, $b) $T` can't depend on `$i` (only `%A` can), so `gauss.kurt` states its axioms for the summand `$i` only -- decide whether (and how) a non-boolean schema variable may depend on a bound variable (soundness-sensitive)

## postponed from the tutorial discussion (2026-09-26)

- TODO `save` as a replay of the accepted input lines instead of a flattened snapshot (keeps proofs checkable, also with `--strict`, keeps labels and open blocks); forbid `save` in files
- TODO shell: pre-fill each input line with the current indentation (readline `set_startup_hook`), so that a backspace dedents
- TODO `use` only *directly* in a `sandbox`/`expect`, not in a proof block nested inside them (two soundness tests need `use P $w` before the block instead)
- TODO get rid of the `;;; ` markers: `expect` with an optional message prefix, and file-level errors (EOF, unclosed blocks, `break` at top level) via `expect` around a `load` of a helper file in a directory the test discovery skips
- TODO minimal core: remove the name-based special cases (`iff`, `not`/`false`, `=`/`iff` for `def`, `exists`/`pick`) so that `minimal.kurt` really is the core; later maybe separate the rule level from the object level (like Isabelle/Pure)

## NEXT

- TODO solve the path puzzle, also check `load ../foo.kurt` whether it works
- TODO add `(%A iff top) implies A` to `prop.kurt` and check some mafi1 example
- TODO allow `let x with F(x)`, or `let F(x)`, or `let x>0`, merge `pick` and `let` to use `unpack_condition`
- TODO why not `f()` ???  what is it?  it should be parsed `(f)` instead of just `f`
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
- TODO what is the difference between `arity f 1` and `prefix f 1`?  
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
- TODO format "latex", also allow custom latex formats
- TODO use the Token.column information
- TODO add syntactic sugar for case distinctions
