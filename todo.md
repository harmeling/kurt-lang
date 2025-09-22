# TODOs

## NEXT

- TODO: who uses `apply_subst`
- TODO: `match_exprs_with_patterns`, check the boolean variable case
- TODO: merge `apply_subst` with `walk`, also replace boolean variables and trigger subs if possible

- TODO impl_elim: are all universal quantifier removed?  (can be done in simplify)
- TODO group.kurt
- TODO check again what rules are hard-coded
- TODO think about short-cut by equality-elim, just compare last two expressions and find the difference, then search for the corresponding equation, this should be much faster
- TODO implement chains
- TODO check conditions in `first-order.kurt`

## TOPICS before releasing 1.0

- TODO get group.kurt working with constants and with `var x, y, z`
- TODO do calculations with integers and reals
- TODO what should go into `minimal.kurt`?  what into `propositional.kurt` and `first-order.kurt`?
- TODO define what get's exported when loading a file, make variables declarations local?
- TODO get coverage of 100% in the unit tests
- TODO test the conditions for forall and exist rules
- TODO 'thus' with one step shorter, for `qed` we use match, for `thus` we use equal (otherwise matching the correct variables is difficult)
- TODO what should be loaded by default?  `minimal.kurt` or `standards.kurt`?
- TODO check all KurtExceptions for ProofError, ParseError, SyntaxError, EvalError
- TODO check the inference for quantifiers, whether there must be more restrictions, or does the renaming handle it?  try to violate them
- TODO `kurt proofs/debug/chains.kurt`: why is the proof ok?  next, turn chain into inequalities, `chain` must be a list of chains
- TODO have `x<y<=z` as a short cut for `x<y and y<=z`, or even store them separately, and also multi-line equations
- TODO local and export features, files should open a new level, but can export statements as axioms ('use') to the level above them
- TODO do multi-line equations and iff, (no indentation necessary, just must be part of a chain, and previous line must be a chain)
- TODO write documentation/tutorial for the language
- TODO refactoring: work through all 'mainstream', can we avoid them?  check also `decorate_reason` and `formula_ref`.  yes, store the reason in the formula, then generate a log string later up, but we don't need the `mainstream` flag anymore, possibly we need it since some impl-elim are also generating logs, similarly, remove the 'filenames' that are passed around
- TODO search all TODO in the code and check whether they are still relevant

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
