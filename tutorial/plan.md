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
    09a-thus     closing a `proof` block by literal match, no re-derivation

THEORIES -- building and reusing bodies of knowledge
-----------------------------------------------------
    10-load      pulling in ready-made theories, e.g. `prop.kurt`
    10a-save     the reverse of `load`: write the theory out to a file
    11-def       introducing a new constant via its defining equation
    12-theory    inspecting the current theory
    13-todo      admitting a step as an exercise/placeholder
    14-sandbox   a scratch block that is thrown away when closed
    14a-commit   keeping a `sandbox`'s content instead of discarding it
    15-expect    a block that must fail, with a named kind of error
    16-local     what a loaded file does and doesn't export

BLOCKS -- natural-deduction-style sub-proofs
-----------------------------------------------
    20-assume    hypothetical reasoning ("impl-intro", "not-intro")
    21-let       introducing a fresh, arbitrary constant ("forall-intro")
    22-pick      extracting a witness from an existential ("exists-elim")
    23-case      case distinctions ("or-elim")
    25-break     abandoning a block immediately, without proving anything
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
    42a-nonassoc an infix operator that rejects being chained, ambiguously
    43-latex     custom LaTeX rendering for a symbol (see `-l` / `latex.kurt`)

MISC -- REPL/output behaviour and self-documentation
--------------------------------------------------------
    50-format    how formulas are printed (`sexpr` vs `normal`)
    51-help      list of all keywords, straight from Kurt itself
    52-hint      toggle: hints for the next input (shell only)
    53-verbose   toggle: show extra detail while matching formulas
    55-calc      toggle: automatic arithmetic simplification (`+`, `*`)

Not covered (deliberately)
---------------------------
    inspect      raises `NotImplementedError` in `kurt.py` -- not usable yet
    fix          old name for what is now the `let` keyword (see `21-let.kurt`)
    indent       removed -- the shell's indentation handling used to differ
                 from a file's (see below); once unified, the toggle (and
                 `done`) had nothing left to switch

File and shell are now handled identically
----------------------------------------------
Indentation is significant everywhere, in the shell exactly as in a file:
`assume`/`let`/`pick`/`proof`/`sandbox`/`expect` blocks all close the same
way, by dedenting -- there is no more `indent` toggle, and no more
`done` (it existed purely to fake a dedent in the shell; once the shell
started reading real indentation, it had nothing left to do that dedenting
didn't already do). Four keywords remain as optional, position-independent
alternatives to dedenting, and all work in files too, not just the shell:
`qed` (09-qed.kurt) and `thus` (09a-thus.kurt) both still need a real
dedent -- `qed` re-derives the shown goal, `thus` only checks the block's
last line already *is* the goal, literally -- while `break` (25-break.kurt)
and `commit` (14a-commit.kurt) need none at all, closing the current block
immediately; `break` discards it, `commit` keeps it (and only ever closes
a `sandbox`, since every other block already has its own way to keep what
happened inside).
