Kurt tutorial -- lesson plan
============================

Each lesson is a single `.kurt` file that teaches exactly one keyword (or,
for `true`/`implies`/`and`, one core built-in symbol).  Lessons are numbered
consecutively (the sections below are just for orientation), and are meant to
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
    11-save      the reverse of `load`: write the theory out to a file
    12-def       introducing a new constant via its defining equation
    13-theory    inspecting the current theory
    14-todo      admitting a step as an exercise/placeholder
    15-sandbox   a scratch block that is thrown away when closed
    16-expect    a block that must fail, with a named kind of error
    17-local     what a loaded file does and doesn't export

BLOCKS -- natural-deduction-style sub-proofs
-----------------------------------------------
    18-assume    hypothetical reasoning ("impl-intro", "not-intro")
    19-let       introducing a fresh, arbitrary constant ("forall-intro")
    20-pick      extracting a witness from an existential ("exists-elim")
    21-case      case distinctions ("or-elim")
    22-break     abandoning a block immediately, without proving anything
    23-mode      what kind of block are we in right now?
    24-trail     the chain of open blocks, one line
    25-context   the chain of open blocks, in detail
    26-level     how deeply nested are we?

SYNTAX -- extending Kurt's grammar from Kurt source
------------------------------------------------------
    27-tokenize  see how a string turns into tokens
    28-parse     see how tokens turn into a term
    29-syntax    inspect all currently declared syntax
    30-infix     declaring infix operators (with binding powers)
    31-prefix    declaring prefix operators
    32-postfix   declaring postfix operators
    33-brackets  declaring bracket pairs
    34-arity     declaring a symbol's number of arguments
    35-bindop    declaring variable-binding operators (`forall`, `exists`, ...)
    36-chain     declaring chains of mixed (in)equalities, e.g. `a = b < c`

SUGAR -- syntactic convenience
---------------------------------
    37-alias     giving a symbol an extra name (e.g. Unicode for ASCII)
    38-flat      an infix operator that doesn't need explicit nesting
    39-sym       an infix operator whose arguments may be swapped

MISC -- REPL/output behaviour and self-documentation
--------------------------------------------------------
    40-format    how formulas are printed (`sexpr` vs `normal`)
    41-help      list of all keywords, straight from Kurt itself
    42-hint      toggle: hints for the next input (shell only)
    43-verbose   toggle: show extra detail while matching formulas
    44-calc      toggle: automatic arithmetic simplification (`+`, `*`)

PUTTING IT ALL TOGETHER -- writing a proof from scratch, not just one keyword
------------------------------------------------------------------------------
    45-worked-proof   a full worked example (de Morgan's law, one direction),
                      narrating the actual process: state the goal, sketch a
                      strategy, hit "can not derive" at least once, and fix it

Not covered (deliberately)
---------------------------
    inspect      raises `NotImplementedError` in `kurt.py` -- not usable yet
    fix          old name for what is now the `let` keyword (see `19-let.kurt`)
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
didn't already do). Two keywords remain as optional alternatives to
dedenting, and both work in files too, not just the shell: `qed`
(09-qed.kurt) still needs a real dedent and re-derives the shown goal, while
`break` (22-break.kurt) needs none at all and discards the current block
immediately.
