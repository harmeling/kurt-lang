# mafi1: proofs from the lecture slides

The proofs of the lecture "Mathematik für Informatik 1" (linear algebra, TU Dortmund) in Kurt,
named after the slide decks. Each file is checked with the tests; run one with
`kurt proofs/mafi1/06-subspaces.kurt`.

## Theories

| file | content |
|---|---|
| `field.kurt` | fields: (K1)–(K9) of deck 07, every axiom for the elements of `K`; Satz 2.24–2.26 |
| `vectorspace.kurt` | vector spaces: (V1)–(V8) of decks 04/05 for every `vectorspace($V)` |
| `tautologies.kurt` | the tautologies that decks 03 and 11a check with truth tables, here by natural deduction |
| `scalar-product.kurt` | inner products: (S1)–(S3) of deck 23, orthogonality, Pythagoras |
| `matrices.kurt` | the rules for matrices that decks 12–30 use without proof (as axioms) |

As on the slides, `+`, `·`, `-` and `0` are the same for scalars and vectors; which axiom
applies is decided by the memberships `λ ∈ K`, `x ∈ V`. A rewriting step may use an axiom with
conditions inside a term: Kurt derives its instance from the memberships and shows it as a step
of its own (`17a`). The memberships themselves are lines of the proof (`0 · $l ∈ K`).

## What is proven

| deck | statements | file |
|---|---|---|
| 01 Mengen | A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) | `001-two-equal-sets.kurt` |
| 03 Formeln | negating ∀ and ∃; A = B ⇔ A ⊂ B ∧ B ⊂ A (as the slides' chain); the two forms of injectivity | `03-formulas.kurt` |
| 04 reelle Vektorräume | the zero vector and the inverse are unique | `vectorspace.kurt` |
| 06 Untervektorräume | 0 ∈ U, −x ∈ U, (V1)/(V3)/(V4) in U; exercise: U ∩ W is a subspace | `06-subspaces.kurt` |
| 07 Körper | 0 = 0 + 0, 0 λ = 0, (−1)(−1) = 1, uniqueness of 0, 1, −λ, λ⁻¹ (exercises), (−1) λ = −λ, no zero divisors (both directions) | `field.kurt` |
| 07 Gruppen | Satz a (right inverse and neutral element work from the left), Satz b (cancellation) | `07-groups.kurt` |
| 08 lineare Unabhängigkeit | L(v, w) is a subspace (for two vectors) | `08-linear-span.kurt` |
| 10 lineare Abbildungen | f(0) = 0, f(x − y) = f(x) − f(y), g ∘ f is linear, Kern f = {0} ⇔ f injective, Bild f = W ⇔ f surjective | `10-linear-maps.kurt` |
| 11a Beweise | ¬A ≡ A ⇒ ⊥, ⊥ ≡ A ∧ ¬A, ex falso, Kontraposition, Fallunterscheidung (as the slides' chains); √2 ∉ ℚ and the Gauss sum are in `../natural-numbers/` | `11a-proofs.kurt` |
| 15 inverse Matrix | B A = E ⇒ B = A⁻¹, correctness of the Gauss-Jordan algorithm, (A⁻¹)ᵀ = A⁻¹ for symmetric A | `15-inverse-matrix.kurt` |
| 18 det und Matrixprodukt | det A ≠ 0 and det(A⁻¹) = det(A)⁻¹; det(C⁻¹ A C) = det A | `18-det-matrix-product.kurt` |
| 23/24 Skalarprodukte, orthogonale Vektoren | ⟨x, 0⟩ = 0, x ⊥ y ⇒ y ⊥ x and x ⊥ λy, Pythagoras, M^⊥ is a subspace, M ∩ M^⊥ = {0} | `scalar-product.kurt`, `24-orthogonal-vectors.kurt` |
| 25 orthogonale Abbildungen | Aᵀ A = E ⇒ det A = ±1 | `25-orthogonal-matrices.kurt` |
| 26 Eigenwerte | λ ≠ μ ⇒ E_λ ∩ E_μ = {0} | `26-eigenvalues.kurt` |
| 28 selbstadjungierte Endomorphismen | eigenvectors for different eigenvalues are orthogonal; f(v^⊥) ⊂ v^⊥ | `28-self-adjoint.kurt` |
| 30 Hauptachsentransformation | D = Pᵀ A P, P Pᵀ = E ⇒ A = P D Pᵀ | `30-principal-axes.kurt` |

## Not (yet) proven

- **Sums with indices** (v₁, …, v_r; matrices entry by entry; Leibniz formula; Gram–Schmidt;
  linear independence, bases, dimension, rank): Kurt has `sum` (analysis.kurt), but no
  tuples of length n yet. Two-vector versions are possible (as `08-linear-span.kurt`).
- **Calculations with ad − bc** (deck 16, the 2×2 determinant): possible, but every
  rearrangement is a line of its own, since Kurt has no normalizer for ring expressions.
- **Cardinality** (deck 03b, Cantor, Cantor–Bernstein) and **real analysis** (√, arccos,
  the fundamental theorem of algebra): out of reach for now.
