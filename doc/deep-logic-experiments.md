# Deeply embedded proof systems in Kurt

Status: executable experiment, 2026-10-08; reviewed 2026-10-09. The experiments do not justify a
generic `rule` keyword.

## Representation

Kurt can serve as a metalogic when object formulas are terms rather than Kurt Booleans:

| role | example | Kurt type |
|---|---|---|
| object formula | `$A`, `$A → $B`, `□$A` | term |
| theorem judgment | `⊢ $A` | Boolean |
| sequent judgment | `$Γ ⊢ $A` | Boolean |
| rule premises | `(⊢ $A) and (⊢ ($A → $B))` | Boolean |
| rule | `PREMISES implies CONCLUSION` | Boolean |

`⊢` is both prefix and infix. These are different arities of one symbol, not an implicit parser
rewrite. The modal theory relates them explicitly:

```kurt
use (⊢ $A) implies (empty ⊢ $A) "theorem-to-empty-sequent"
use (empty ⊢ $A) implies (⊢ $A) "empty-sequent-to-theorem"
```

This makes necessitation an ordinary meta-level implication:

```kurt
use (⊢ $A) implies (⊢ □$A) "necessitation"
```

It does not assert the object formula `$A → □$A`.

## Executable experiments

- `src/kurt/theories/modal.kurt` gives a classical implicational Hilbert basis, modal K,
  T, object propositional connectives, duality, distribution, object modus ponens, and
  necessitation. `proofs/modal-logic/deep-embedding.kurt` instantiates
  each important part and crosses between prefix theoremhood and the empty-context sequent.
- `proofs/logic-encodings/sequent-implication.kurt` represents contexts with `empty` and
  `extend Γ A`. Assumption, weakening, implication right, and implication elimination are Kurt
  schemata. It proves `⊢ (P → P)` through an explicit empty-context derivation.
- `proofs/logic-encodings/ordered-resources.kurt` is an ordered multiplicative fragment. Tensor
  introduction splits an ordered pair of contexts. Expected-error regressions confirm that the
  fragment supplies no exchange, weakening, or contraction. Kurt's metalogical `and` may reorder
  the two rule premises; it does not reorder either represented object context.

The experiments show that modal necessitation, ordinary sequents, and at least a small
substructural calculus do not require a new language keyword.

## Limits found

The modal experiment first exposed that the Boolean/non-Boolean distinction could not declare an
object constructor such as `→` permanently non-Boolean. Kurt now has optional nominal sorts:
`modal.kurt` declares `sort formula` and gives `→`, `□`, and its schema variables sparse
`formula` signatures. These declarations remain optional, do not choose `const` or `var`, and
are enforced when schemas are instantiated as well as when source is parsed. `bool` remains the
reserved sort of Kurt judgments. Generic equality and unmentioned operator positions remain
deliberately unconstrained; there is no subtyping, inference, or mandatory type system.

All symbols also have one global owner. `modal.kurt`'s object `→` cannot coexist with
`set.kurt`'s function-space `→`, and its object `∧` cannot coexist with `prop.kurt`'s Boolean
alias. Namespaces or explicitly sorted notation would be needed to combine such theories safely.

`lambda.kurt` tests object languages with binders. A de Bruijn representation expresses complete
syntax-directed simply typed lambda-calculus rules through explicit contexts. A named `λ` binder
also gives alpha equivalence and capture-avoiding beta substitution, although full named
hypothetical-context typing is not convenient in the current rule language. The theory now has
weak compatible beta rules and a deterministic call-by-value relation. Executable experiments
check a concrete preservation instance and a finite confluence diamond. General preservation and
Church–Rosser still require induction over represented derivations, a substitution lemma, and a
transitive or parallel reduction relation; stating them as bare axioms would not be an experiment.

Conclusion: ordinary Boolean schemata already express every rule exercised here. A generic
`rule` would either duplicate `use PREMISES implies CONCLUSION`, or add assumption-discharge and
proof-object semantics that these experiments do not require. The named-lambda limitation is a
representation and notation problem, not evidence for that language feature. Reconsider only if
a future executable encoding exposes a concrete rule that cannot be stated as a Kurt schema.
