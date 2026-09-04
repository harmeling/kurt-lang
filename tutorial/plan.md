Kurt tutorial -- lesson plan
============================

Each lesson is a single `.kurt` file that teaches exactly one keyword (or,
for `true`/`implies`/`and`, one core built-in symbol).  Lessons are meant to
be read and run in numeric order: a lesson only uses keywords that were
already introduced in an earlier lesson (plus whatever `minimal.kurt`
hard-codes for free: `true`, `implies`, `and`, brackets, comma, space).

Run a lesson with:

    kurt tutorial/00-true.kurt

BASICS -- your first checked proofs
------------------------------------
    00-true      the only thing provable from nothing
    01-bool      declaring symbols as booleans (propositions)
    02-use       adding axioms to the theory
    03-implies   built-in implication, modus ponens ("impl-elim")
    04-and       built-in conjunction, "and-intro" (and one "and-elim" example)
    05-const     declaring constants (fixed, specific objects)
    06-var       declaring variables (stand-ins for arbitrary objects)
    07-show      stating a goal to be proved
    08-proof     opening the block that proves a `show`n goal
    09-qed       closing a `proof` block

THEORIES -- building and reusing bodies of knowledge
-----------------------------------------------------
    10-load      pulling in ready-made theories, e.g. `prop.kurt`
    11-def       introducing a new constant via its defining equation
    12-theory    inspecting the current theory
    13-todo      admitting a step as an exercise/placeholder
    14-sandbox   a scratch block that is thrown away (REPL-only to close)

BLOCKS -- natural-deduction-style sub-proofs
-----------------------------------------------
    20-assume    hypothetical reasoning ("impl-intro", "not-intro")
    21-let       introducing a fresh, arbitrary constant ("forall-intro")
    22-pick      extracting a witness from an existential ("exists-elim")
    23-case      case distinctions ("or-elim")
    24-done      closing assume/let/pick blocks (REPL-only)
    25-break     abandoning a block without proving anything (REPL-only)
    26-mode      what kind of block are we in right now?
    27-trail     the chain of open blocks, one line
    28-context   the chain of open blocks, in detail
    29-level     how deeply nested are we?

SYNTAX -- extending Kurt's grammar from Kurt source
------------------------------------------------------
    30-tokenize  see how a string turns into tokens
    31-parse     see how tokens turn into a term
    32-syntax    inspect all currently declared syntax
    33-infix     declaring infix operators (with binding powers)
    34-prefix    declaring prefix operators
    35-postfix   declaring postfix operators
    36-brackets  declaring bracket pairs
    37-arity     declaring a symbol's number of arguments
    38-bindop    declaring variable-binding operators (`forall`, `exists`, ...)
    39-chain     declaring chains of mixed (in)equalities, e.g. `a = b < c`

SUGAR -- syntactic convenience
---------------------------------
    40-alias     giving a symbol an extra name (e.g. Unicode for ASCII)
    41-flat      an infix operator that doesn't need explicit nesting
    42-sym       an infix operator whose arguments may be swapped
    43-latex     custom LaTeX rendering for a symbol (see `-l` / `latex.kurt`)

MISC -- REPL/output behaviour and self-documentation
--------------------------------------------------------
    50-format    how formulas are printed (`sexpr` vs `normal`)
    51-help      list of all keywords, straight from Kurt itself
    52-hint      toggle: hints for the next input (shell only)
    53-verbose   toggle: show extra detail while matching formulas
    54-indent    toggle: indentation-based block structure in the shell
    55-calc      toggle: automatic arithmetic simplification (`+`, `*`)

Not covered (deliberately)
---------------------------
    inspect      raises `NotImplementedError` in `kurt.py` -- not usable yet
    thus         mentioned in `doc/kurt-notes.md`/`todo.md` as a future,
                 not-yet-implemented shortcut for `qed`/equational proofs
    fix          old name for what is now the `let` keyword (see `21-let.kurt`)

Notes on things that turned out to be REPL-only
--------------------------------------------------
`done`, `break`, and closing a `sandbox` block all require the interactive
shell in `indent` mode -- a `.kurt` *file* cannot use them at all (dedenting
in a file closes `assume`/`let`/`pick`/`proof` blocks automatically, but
raises a `ParseError`/`EvalError` for `done`, `break`, or an unclosed
`sandbox`).  Lessons 14, 24 and 25 therefore show an annotated transcript of
a shell session in comments, rather than runnable block-closing code.
