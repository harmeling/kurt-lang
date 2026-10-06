# The Kurt tutorial

Task by task, one lesson each: "How do I prove an implication?", "How do I introduce a universal
quantifier?", or "Why did this step fail?" Every lesson is a Kurt file: run it
(`kurt 02-prove-an-implication.kurt`), change it, run it again. (It used to be the cookbook,
`doc/kurt-cookbook.md`.)

- [`00-check-a-proof-file.kurt`](00-check-a-proof-file.kurt): Check a proof file
- [`01-apply-an-implication-modus-ponens.kurt`](01-apply-an-implication-modus-ponens.kurt): Apply an implication: modus ponens
- [`02-prove-an-implication.kurt`](02-prove-an-implication.kurt): Prove an implication
- [`03-prove-a-negation-by-contradiction.kurt`](03-prove-a-negation-by-contradiction.kurt): Prove a negation by contradiction
- [`04-split-into-cases.kurt`](04-split-into-cases.kurt): Split into cases
- [`05-rewrite-with-equality.kurt`](05-rewrite-with-equality.kurt): Rewrite with equality
- [`06-define-a-constant-or-function.kurt`](06-define-a-constant-or-function.kurt): Define a constant or function
- [`07-instantiate-a-universal-fact.kurt`](07-instantiate-a-universal-fact.kurt): Instantiate a universal fact
- [`08-prove-a-universal-fact.kurt`](08-prove-a-universal-fact.kurt): Prove a universal fact
- [`09-use-an-existential-witness.kurt`](09-use-an-existential-witness.kurt): Use an existential witness
- [`10-use-exact-arithmetic-with-calc.kurt`](10-use-exact-arithmetic-with-calc.kurt): Use exact arithmetic with `calc`
- [`11-prove-a-statement-by-induction.kurt`](11-prove-a-statement-by-induction.kurt): Prove a statement by induction
- [`12-write-and-load-a-reusable-theory.kurt`](12-write-and-load-a-reusable-theory.kurt): Write and load a reusable theory
- [`13-check-that-a-bad-proof-is-rejected.kurt`](13-check-that-a-bad-proof-is-rejected.kurt): Check that a bad proof is rejected
- [`14-develop-an-unfinished-proof-safely.kurt`](14-develop-an-unfinished-proof-safely.kurt): Develop an unfinished proof safely
- [`15-understand-why-a-step-succeeded.kurt`](15-understand-why-a-step-succeeded.kurt): Understand why a step succeeded
- [`16-diagnose-can-not-derive.kurt`](16-diagnose-can-not-derive.kurt): Diagnose “can not derive”
- [`17-grade-student-proofs-with-strict-mode.kurt`](17-grade-student-proofs-with-strict-mode.kurt): Grade student proofs with strict mode
- [`18-choose-the-theory-to-load.kurt`](18-choose-the-theory-to-load.kurt): Choose the theory to load
- [`19-common-mistakes.kurt`](19-common-mistakes.kurt): Common mistakes
- [`20-constants-variables-and-declarations.kurt`](20-constants-variables-and-declarations.kurt): Constants, variables, and what declares them
- [`21-worked-proof.kurt`](21-worked-proof.kurt): A worked proof, from a blank file
- [`22-prove-a-law-of-logic.kurt`](22-prove-a-law-of-logic.kurt): Prove a law of logic (contraposition)
- [`23-work-with-pairs-and-tuples.kurt`](23-work-with-pairs-and-tuples.kurt): Work with pairs and tuples
- [`24-use-a-structure-groups.kurt`](24-use-a-structure-groups.kurt): Use a structure: groups

The lessons of [`keywords/`](../keywords/) explain Kurt's keywords and ideas one by one, and
[`doc/kurt-doc.md`](../doc/kurt-doc.md) is the complete language reference. More examples:

- `proofs/natural-deduction/`: implication, negation, cases, quantifiers, and equality.
- `proofs/arithmetic/`: calculation, algebraic rewriting, order, exponents, and factorial.
- `proofs/natural-numbers/`: induction, Peano-style examples, √2 is irrational.
- `proofs/set-theory/`: membership, products, powersets, tuples, and mappings.
- `proofs/analysis/`: maxima, suprema, and epsilon-delta limit proofs.
- `proofs/mafi1/`: the proofs of a linear algebra lecture.
- `proofs/soundness/`: adversarial examples showing what Kurt must reject.
