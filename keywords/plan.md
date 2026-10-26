Kurt keywords -- lesson plan
============================

Each lesson is a single `.kurt` file that teaches exactly one keyword (or,
for `true`/`implies`/`and`, one core built-in symbol).  Lessons are numbered
consecutively (the sections below are just for orientation), and are meant to
be read and run in numeric order: a lesson only uses keywords that were
already introduced in an earlier lesson (plus whatever `minimal.kurt`
hard-codes for free: `true`, `implies`, `and`, brackets, comma, space),
except where the lesson says so (07-show uses `proof`/`qed`, 08-proof `qed`).

Run a lesson with:

    kurt keywords/00-true.kurt

BASICS -- your first checked proofs
------------------------------------
    00-true      the only thing provable from nothing
    01-prop      declaring the statement places of symbols
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
    10-load      pulling in ready-made theories, e.g. `propositional.kurt`
    11-save      keep what you did: write the accepted lines out to a file
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
    21-case      case distinctions (the derived, kernel-checked "case-elim")
    22-break     giving up the innermost open thing: a block (in a proof, only the proof), then the claim
    23-summary   where the proof is: open blocks, claims to prove, next steps

SYNTAX -- extending Kurt's grammar from Kurt source
------------------------------------------------------
    24-tokenize  see how a string turns into tokens
    25-parse     see how tokens turn into a term
    26-syntax    inspect all currently declared syntax
    27-infix     declaring infix operators (with binding powers)
    28-prefix    declaring prefix operators
    29-postfix   declaring postfix operators
    30-brackets  declaring bracket pairs
    31-arity     declaring a symbol's number of arguments
    32-bindop    declaring variable-binding operators (`forall`, `exists`, ...)
    33-chain     declaring chains of mixed (in)equalities, e.g. `a = b < c`

SUGAR -- syntactic convenience
---------------------------------
    34-alias     giving a symbol an extra name (e.g. Unicode for ASCII)
    35-flat      an infix operator that doesn't need explicit nesting
    36-sym       an infix operator whose arguments may be swapped

MISC -- REPL/output behaviour and self-documentation
--------------------------------------------------------
    37-format    how formulas are printed (`normal`, `sexpr`, `source`)
    38-help      list of all keywords, straight from Kurt itself
    39-hint      toggle: hints for the next input (shell only)
    40-calc      computing with numbers: `builtin + add`, `builtin < lt`, ...; `calc on`/`off`

TRUST -- certificates
---------------------
    41-cert      `cert N`: the certificate of a line, checked by the kernel;
                 `.kurtc` files and `kurt --deps`

DEBUGGING
---------
    42-breakpoint  stop in a file and continue in the shell with its state
    43-list        which theories are loaded, and what each one exports

OPTIONAL SORTS
--------------
    44-sort        sorts: kinds of objects below `any`, subsorts, the first sorted use is final, `default`
    47-default     the sort of the new symbols of a file: at the first appearance, unless the line says otherwise

MEANINGS BUILT INTO KURT
------------------------
    45-builtin     a calculator operation (`builtin + add`) or a role of the engine (`builtin iff equivalence`)

NOTATION
--------
    46-inline      a definition applied while reading (`x > 0` is `0 < x`), and why not every `def` is one

File and shell are handled identically
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
immediately -- in the `proof` of a `show` only the proof, the claim stays
open; a second `break` withdraws the claim.
