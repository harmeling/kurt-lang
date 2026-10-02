# The Kurt Programming Language Cookbook

Kurt is a proof language for writing short, readable mathematical arguments and checking each
step automatically. This cookbook answers task-oriented questions: “How do I prove an
implication?”, “How do I introduce a universal quantifier?”, or “Why did this step fail?”

If you are new to Kurt, work through `tutorial/00-true.kurt` to
`tutorial/45-worked-proof.kurt` first. Use `doc/kurt-doc.md` when you need the complete language
reference. The recipes here assume that you know what `bool`, `use`, `show`, `proof`, and `qed`
mean.

Every complete `.kurt` example in this document is intended to run as written.

## 1. Check a proof file

Save a proof as `proof.kurt`, then run:

```console
kurt proof.kurt
```

A finished proof ends with `Proof checked`. A failed check exits with status 1 and identifies the
source line. A file containing `todo` ends with `Proof almost checked: N todos` and exits with
status 0 because each `todo` is an explicit admission rather than an unexpected failure.

Useful command-line variants:

```console
kurt -v proof.kurt          # show extra matching information
kurt -s proof.kurt          # strict grading mode
kurt --no-kurtc proof.kurt  # do not read or write certificate caches
kurt --deps proof.kurt      # show the load-dependency tree
kurt -i proof.kurt          # check the file, then continue interactively
```

## 2. Apply an implication: modus ponens

If the theory contains `A implies B` and `A`, write `B`. Kurt applies implication elimination
automatically.

```kurt
bool A, B, C

use A implies B  "A-to-B"
use A
B

use B implies C  "B-to-C"
C
```

Kurt performs one inference step at a time. It derives `B` first and can then use that new fact to
derive `C`.

## 3. Prove an implication

To prove `A implies C`, assume `A`, derive `C`, and leave the `assume` block. Closing the block
discharges the assumption and applies implication introduction.

```kurt
bool A, B, C
use A implies B
use B implies C

show A implies C
proof
    assume A
        B
        C
qed
```

The facts proved inside the block do not leak out individually. The result that leaves the block
is `A implies C`.

## 4. Prove a negation by contradiction

Load propositional logic for `not`, `false`, and their rules. Assume the proposition you want to
negate and derive `false`.

```kurt
load prop
bool p, q

use p implies q
use not q

show not p
proof
    assume p
        q
        false
qed
```

Here `q` contradicts `not q`, so Kurt derives `false`. Closing `assume p` then derives `not p`.

## 5. Split into cases

For a proof from `A or B`, prove the same conclusion in an `A` case and a `B` case. The
propositional theory's `or-elim` rule combines the disjunction and the two implications produced
by closing the case blocks.

```kurt
load prop
bool A, B, C

use A or B
use A implies C
use B implies C

show C
proof
    case A
        C
    case B
        C
    C
qed
```

A `case` block behaves like `assume` when it closes: the first block produces `A implies C`, and
the second produces `B implies C`. The final `C` is the explicit `or-elim` step.

For more than two alternatives, combine the cases in stages. `or` is flat and symmetric, but the
current search is deliberately single-hop; an intermediate implication or conclusion is often
needed.

## 6. Rewrite with equality

Load `equality` for reflexivity and Leibniz substitution. If `a = b` and a fact contains `a`, Kurt
can replace that occurrence with `b`.

```kurt
load equality
const a, b, f
arity f 1

use a = b
use f(a) = a
f(b) = a
```

The last step uses the labelled rule `equal-elim` from `equality.kurt`. Equality is symmetric, so
Kurt can also use an equation in the other direction.

When a rewrite does not happen, state an intermediate expression showing exactly one replacement.
Kurt is a one-step checker, not a multi-step simplifier.

## 7. Define a constant or function

`def` gives one new symbol a conservative definition. Load `prop` for definitions with `iff`, or
`equality`/`arith` for definitions with `=`.

```kurt
load arith
calc on

def four = 2 + 2
four = 4

def square($x) = $x * $x
square(3) = 9
square(5) = 25
```

The left side must contain exactly one new symbol, optionally applied to distinct variables. All
variables on the right must also occur on the left. These are rejected because they are not
conservative definitions:

```text
def c = $x             ; an unconstrained variable appears only on the right
def f($x, $x) = $x     ; repeated parameter
def c * 0 = 1          ; the new symbol is not the defined head of a term
```

Use `use` for an axiom and `def` only for introducing a name whose meaning is fixed by existing
terms.

## 8. Instantiate a universal fact

Load `logic` for quantifier inference rules. A universally quantified fact can be instantiated at
a particular value:

```kurt
load logic
bool P
arity P 1
const P, c

use forall $x P($x)
P(c)
```

`$x` is the bound variable. `P(c)` follows by the `forall-elim` rule in `logic.kurt`.

## 9. Prove a universal fact

Use `let` to introduce a fresh, arbitrary object. Prove the body for that object, then close the
block. Kurt applies universal introduction.

```kurt
load logic, equality

show forall $x ($x = $x)
proof
    let x
        x = x
qed
```

The introduced name must be fresh. The conclusion may not depend on an unrelated local constant
from inside the block.

For a conditioned quantifier, put the condition in the `let` line. The condition is available as
an assumption inside the block:

```kurt
load logic, arith

show forall $x > 0 ($x > 0)
proof
    let x > 0
        x > 0
qed
```

## 10. Use an existential witness

`pick` opens a block around a fresh witness obtained from an existential fact. The conclusion
leaving the block must not mention the witness.

```kurt
load logic
bool P, B, C
arity P 1
const P, B, C

use forall $x (P($x) implies B)
use B implies C
use exists $x P($x)

show C
proof
    pick a with P(a)
        P(a) implies B
        B
    C
qed
```

Inside the block, `a` is one particular but unknown witness and `P(a)` is available. Closing the
block preserves `C` because `C` does not mention `a`.

If the existential itself has a condition, first use `exists-cond-def` to rewrite it to an
ordinary existential whose body is a conjunction, then pick from that form.

## 11. Use exact arithmetic with `calc`

`calc on` enables exact computation for the symbols bound by `arith.kurt`. Integers, finite
decimals, and fractions are represented exactly; Kurt does not use binary floating-point
approximations for proof steps.

```kurt
load arith
calc on

2 + 3 = 5
0.1 + 0.2 = 0.3
2 ^ 10 = 1024
7 / 2 = 3.5
```

`calc` computes when all required values are known. It does not solve equations for unknowns. For
example, matching `$b / 3` against `0` does not infer `$b = 0`; state or prove that algebraic step
using theory rules.

Turn calculation off when you need an unreduced expression as a rewrite target:

```text
calc off
use 8 = 2 ^ 3
```

## 12. Prove a statement by induction

`natural.kurt` provides the induction principle. Supply the base case and induction step as one
conjunction, because application of the induction rule is a single inference step.

```kurt
load natural
bool P
arity P 1
const P

use P(0) and (forall $n in Nat (P($n) implies P($n + 1)))  "base-and-step"

forall $n in Nat P($n)
forall $n ($n in Nat implies P($n))
5 in Nat implies P(5)
```

For a real proof, derive the base and step in a preceding proof block instead of introducing them
with `use`. Keep the resulting conjunction available as one fact before invoking induction.

## 13. Write and load a reusable theory

A theory is an ordinary `.kurt` file. Facts cross a `load` boundary only when they have a label
and are not marked `local`.

Create `my-theory.kurt`:

```kurt
load prop
bool P, Q

use P implies Q  "P-to-Q"
use P            "P"
use Q local      "internal-helper"
```

Then use it from another file:

```kurt
load my-theory

P
P implies Q
Q
```

The labelled facts `P` and `P implies Q` are exported. The `local` fact stays inside
`my-theory.kurt`. Unlabelled facts also stay local. A symbol declaration travels with an exported
fact when that fact needs it; there is no separate export declaration.

Give labels stable, descriptive names. They appear in proof reasons and make exported theory APIs
clearer.

## 14. Check that a bad proof is rejected

Use `expect "KIND"` for an example or regression that should fail. It checks the category of the
error, not fragile message wording.

```kurt
bool A, B
use A

expect "ProofError"
    B

true
```

Supported kinds are `ProofError`, `ParseError`, `EvalError`, `SyntaxError`, and `TypeError`. If the
block succeeds instead of raising the named error, the expectation itself fails.

Use this pattern in teaching material and most negative regression proofs. Only test exact error
text when the wording itself is the behavior under test.

## 15. Develop an unfinished proof safely

Use `todo FORMULA` when a known gap should remain visible in the final result:

```kurt
load prop
bool A, B

show A implies B
proof
    assume A
        todo B
qed
```

Use `sandbox` for experiments that must not affect the surrounding theory:

```kurt
bool A
use A

sandbox
    use B
    B

A
expect "ProofError"
    B
```

Use `break` to abandon an open block immediately. A sandbox is discarded whether it closes by a
dedent or by `break`.

## 16. Understand why a step succeeded

Kurt prints a short reason beside every accepted formula. Labels replace raw source locations
when available. For more detail, use `cert` after a step:

```kurt
bool A, B
use A implies B  "modus-ponens"
use A
B
cert 4
```

The certificate shows:

- the goal,
- the rule or fact used,
- variable instantiations,
- premises and their source locations, and
- the kernel's verdict.

`cert` without a line number shows the most recent line with a certificate. `verbose` prints more
matching information while checking, but `cert` is usually the clearer first tool.

## 17. Diagnose “can not derive”

Kurt searches for one justified inference at a time. A mathematically true conclusion may still
need intermediate lines. When a line fails:

1. Check that the required theory is loaded. `not`/`or` need `prop`, equality needs `equality`,
   quantifier rules need `logic`, and arithmetic rules need `arith`.
2. Check the exact parsed form with `parse EXPRESSION`, especially around precedence, function
   application, and custom operators.
3. Use `theory` or `theory OPERATOR` to see which facts are currently available.
4. Write the missing intermediate conclusion explicitly. Do not expect multi-hop search.
5. For an implication rule, make its entire premise available as facts. Some rules require a
   conjunction as one fact, notably induction.
6. Check whether a fact was kept inside a block or was not exported by a loaded file.
7. Turn `calc` on only when concrete arithmetic should be normalized; turn it off when the
   unreduced expression is needed for a rewrite.
8. Use `cert` on the preceding successful step to compare its exact formula with the failed goal.

A good development loop is:

```text
show GOAL
proof
    ; write the intended strategy as comments
    ; try one small inference
    ; if it fails, add the missing bridge as another line
qed
```

The complete version of this workflow, including a deliberate failed attempt and repair, is
`tutorial/45-worked-proof.kurt`.

## 18. Grade student proofs with strict mode

Strict mode rejects unproven `use`, `todo`, and `chain` statements outside trusted theories. It
also requires symbols to be declared before use.

```console
kurt --strict student-proof.kurt
```

To provide instructor-approved axioms, put theory files in a separate directory and mark that
directory trusted with `-p`:

```console
kurt --strict -p course-theories student-proof.kurt
```

The student file must prove its claims from Kurt's packaged theories and the theories in
`course-theories`. Do not put solution facts in a theory students can edit.

For exercises under development, `todo` is useful outside strict mode. For submitted work, strict
mode ensures that a remaining `todo` or ad hoc axiom is an error rather than partial success.

## 19. Choose the theory to load

| Theory | Main contents |
|---|---|
| `prop` | `not`, `or`, `iff`, contradiction, propositional introduction/elimination rules |
| `logic` | `forall`, `exists`, conditioned quantifier rules; loads `prop` |
| `equality` | `=`, `!=`/`≠`, reflexivity and substitution; loads `prop` |
| `set` | membership, subsets, separation, union/intersection, products, tuples, mappings |
| `arith` | exact calculation bindings, algebraic laws, order, powers, factorial |
| `natural` | natural-number membership and induction |
| `analysis` | absolute value, finite sums, extrema, suprema/infima, limits |
| `group` | reusable group structure and derived group theorems |

Dependencies are loaded transitively. For example, `load natural` brings in `set`, `logic`,
`equality`, `prop`, and `arith` as required. Use `kurt --deps FILE` to inspect the actual tree.

The packaged `modal` file is an experimental example, not a mature theory. It demonstrates
box/diamond syntax and several sound modal axiom schemata, but it is not a complete proof system
for normal modal logic K or T because Kurt cannot yet express the necessitation rule.

## 20. Common mistakes

| Symptom | Likely cause | Remedy |
|---|---|---|
| `can not derive` a true statement | More than one inference step is missing | Add intermediate claims explicitly |
| A connective is treated like an undeclared symbol | Its theory was not loaded | Load `prop`, `logic`, `equality`, or `arith` as appropriate |
| A quantified proof leaks a local name | A `let`/`pick` witness appears in the conclusion | Generalize it with `let`, or prove a witness-independent result |
| A loaded fact is unavailable | It is unlabelled or marked `local` | Give intended public facts stable non-local labels |
| A rule with several premises does not fire | The complete premise is not available in the expected form | Derive or combine the premises first |
| Arithmetic does not simplify | `calc` is off or an unknown must be solved for | Enable `calc` for concrete values; use algebraic rules for unknowns |
| A rewrite changes too much or too little | The desired substitution is not a single obvious match | State a closer intermediate equality |
| A file passes but is unfinished | It contains `todo` | Read the final todo list; run strict mode for grading |
| A custom theory loads but exports nothing | Its useful facts have no labels | Label each fact that forms the theory's public API |

## Further examples

- `proofs/natural-deduction/`: implication, negation, cases, quantifiers, and equality.
- `proofs/arithmetic/`: calculation, algebraic rewriting, order, exponents, and factorial.
- `proofs/natural-numbers/`: induction and Peano-style examples.
- `proofs/set-theory/`: membership, products, powersets, and tuples.
- `proofs/algebra/groups.kurt`: definitions and derived results for an abstract operation.
- `proofs/analysis/`: maxima, suprema, and epsilon-delta limit proofs.
- `proofs/soundness/`: adversarial examples showing what Kurt must reject.

When a recipe and the full reference differ, `doc/kurt-doc.md` is authoritative for current
syntax and behavior. `doc/kurt-soundness.md` explains the restrictions that protect proof
validity, especially around substitution and quantified variables.
