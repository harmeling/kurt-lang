# Changelog

## 0.7.4 (2026-10-06)

- The lessons: the tutorial has 25 lessons now -- new: 20 constants, variables and declarations,
  21 a worked proof, 22 a law of logic, 23 pairs and tuples, 24 a structure (groups); `keywords/`
  has one lesson per keyword; helper files have no number (`my-theory.kurt`, `local-helper.kurt`).
- `proofs/mafi1/` has English file names (`vectorspace.kurt`, `field.kurt`, ...).
- kurt-doc §11.1: features not implemented, maybe never (`calc` that solves, `def` by pattern
  matching, a ring normalizer), and why.
- `def` introduces a new symbol on its right side as any line does (`def r = g b` with a new `g`),
  and a declared operator isn't new: `def q = ⟨b, b⟩` failed when `,` wasn't used before.
- `arith.kurt` is now `numbers.kurt`: write `load numbers`.
- A symbol is declared by one file only: two theories that both declare `+` (numbers.kurt and a
  structure like a field) can't be loaded together -- the laws of one would hold for the other.
- The variable of a binder with a condition is decided when the line is read -- the first symbol
  of the condition, as written, that is new or a variable -- and kept: `∀ x > 0 ...` works with a
  new plain `x`, and a binder binds the same variable after a block closes.
- doc/kurt-doc.md §3.4 and tutorial lesson 20: which line declares what (constants, variables,
  the automatic declarations, `--strict`).
- Faster: the search is about a quarter faster (natural.kurt 7.9 s → 4.9 s), with the same
  results and reasons -- an index of the theory, remembered answers about symbols, and a
  prefilter of the rules (doc/dev-notes.md).
- `kurt --json FILE` and `CheckResult.events`: each printed line as a record (its line, id, kind,
  rule, the lines it uses, label, comment), the error with its line, the todos -- for graders and
  editors.

## 0.7.3 (2026-10-05)

- Three or four `case` blocks in a row for `A or B or C` (or four alternatives): "or-elim-3" and
  "or-elim-4" in prop.kurt, proven from "or-elim".
- Kurt as a library: `kurt.check_text`, `kurt.check_file`, and sessions with their own options
  (`RunConfig`: strict, paths, kurtc) and state, so that checks in one process don't influence
  each other. `import kurt` gives only this API now; the internals are in `kurt.kurt`.
- "iff-true-elim" and "iff-true-intro" in prop.kurt: what is equivalent to `true` holds, and
  what holds is equivalent to `true`.
- A comma list prints as written: `⟨a, b⟩`, `(a, b)`, `{a, b}` (was `⟨ (a , b) ⟩`, `(a , b)`).
- doc/kurt-doc.md §3.1: Kurt doesn't curry, `(f x) y` and `f x y` are different terms.
- `cert 12-15` shows the certificate of the result of the block of lines 12 to 15.
- Fix: inside an `expect`, a line that closed a nested block and then failed wasn't caught by the
  `expect` (proofs/debug/expect-after-a-nested-block.kurt).
- The result of a block is numbered by the lines of the block, `; 11-13 by impl-intro`, not by
  the next line (which has a step of its own): `by or-elim(14-15, 11-13, 25)` names the blocks.

## 0.7.2 (2026-10-05)

- `pick` from an existential with a condition: `pick c with c > 0 ∧ P c` from `∃ $y > 0 P $y`.
- `argmax` and `argmin` over a set in analysis.kurt (`argmax $v ∈ A T`, *some* place of the
  maximum, only if one exists).
- The reasons of trivial steps name the expected rule: `a = a` is "by equal-intro", `A and A`
  "by and-intro" (the search tries facts first, the rules that fit almost anything last).
- A smaller kernel: its own alpha-equivalence and binder reading, no code shared with the search
  (checked by a test).
- `alias` only for a new name, without declarations of its own (set.kurt had `bool ∈ 0`).
- A crash when a substituted value contained a binder over the replaced variable.
- "TU Dortmund" in the README and `CITATION.cff`.
- `proofs/linear-algebra/cauchy-schwarz.kurt`: the Cauchy-Schwarz inequality for an inner product
  (was in `proofs-not-yet`). For it: arith.kurt's "gt-ne" (`$a > $b ⇒ $a ≠ $b`) and
  "sub-ge-zero" (`$a - $b >= 0 ⇒ $a >= $b`), and the excluded middle in prop.kurt, proven there
  from "not-elim".
- `proofs/natural-numbers/square-root-two-is-irrational.kurt` (was in `proofs-not-yet`): even
  and odd numbers, "every natural number is even or odd" by induction, the square of an odd number
  is odd, and the irrationality of the square root of 2 -- assuming that no natural number is even
  and odd, and that a positive rational is m / n with m, n not both even. For it: natural.kurt's
  "nat-add" and "nat-mul" (sums and products of natural numbers are natural numbers), and
  arith.kurt's "div-mul-div" and "mul-ne-zero".
- `proofs/mafi1/`: the proofs of the lecture "Mathematik für Informatik 1" (linear algebra) that
  fit Kurt: fields, vector spaces, subspaces, groups, linear maps, the span of two vectors,
  inner products, orthogonal complements, eigenspaces, self-adjoint maps, and derivations with
  matrices and determinants -- with each axiom for the elements of its set (`λ ∈ K`, `x ∈ V`), as
  on the slides. An index is in `proofs/mafi1/README.md`.
- `\cdot` is `·`.
- The tutorial is new: `tutorial/`, 20 lessons task by task (made from the cookbook,
  `doc/kurt-cookbook.md`, which is gone). The old tutorial, one keyword or idea per lesson, is
  `keywords/` now.
- `kurt foo.kurtc`: the certificates of `foo.kurt`, readable, line by line (as `cert` shows them).
- The tests check the proof files in 4 processes at once (`KURT_TEST_JOBS`).
- A faster search for rewriting steps: the subterms where the goal differs from one of the latest
  facts are tried first (the tests take a fifth less time).
- A faster search: a formula that can't unify with a premise is skipped without trying (the tests
  take about a third less time).

- natural.kurt: `0 <= n`, `n + 1 ≠ 0`, the predecessor, no natural number between n and n + 1,
  the well-ordering principle (proven from induction), even and odd numbers (none is both), and
  divisibility `∣` (`\mid`) with `coprime`.
- integer.kurt (`Int`) and rational.kurt (`Rat`), with every positive rational in lowest terms
  ("lowest-terms", proven from the well-ordering). `square-root-two-is-irrational.kurt` now only
  assumes what it needs of the square root of 2.
- scripts/kurt2latex.py: all symbols as LaTeX (also `∘`, `·`, `×`, `⟨ ⟩`, Greek letters, and in
  the comments), `$a` as *a*, names upright (`\mathrm{inv}`), and a line with a comment in one row.
- A file with stored certificates for a conditional rewriting step failed on the next run: the
  search after a stored certificate that didn't fit was the plain one, without the shortcuts.
- Conditional rewriting: a rewriting step may use a rule with conditions that are facts
  (`$a ∈ K ⇒ 1 · $a = $a` with `b ∈ K` for `c · (b · 1)` → `c · b`); the instance is shown as a
  step of its own (`17a`). proofs/mafi1/ is 168 lines shorter for it.
- `f(x)` without a space is one term, binding more tightly than `f x`: `inv det(A)` is
  `inv (det A)`, and `∀ $x ∈ Perp(M) ...` reads `Perp(M)` as part of the condition.
- logic.kurt: "forall-iff" and "exists-iff", for rewriting under a quantifier.
- Found by the search now: `⊥` from `∀ x P(x)` and `¬(∀ x P(x))`, and a `∀` formula out of a
  conjunction.
- The kernel shares no code with the search any more (also not for the conditions of `let`), and
  sees the knowledge base only through a read-only snapshot during a check.
- The scope of a binder: only its condition and its last argument, the body -- the range of a `sum`
  and the point of a `lim` are outside, as in mathematics (in `sum x (0, n) (sum x (0, x) x)`,
  the inner range is the outer `x`). Before, every argument was inside.
- set.kurt: mappings are sets of pairs, as in ZF (`f ∈ (A → B)` means `f ⊂ A × B` with exactly one
  pair `(a, f a)` for each `a ∈ A`), so function extensionality holds ("function-extensionality").
  Before, a mapping was an opaque object, and every object was in `∅ → B`.
- `calc on` proves memberships like `3 ∈ Nat`, `-3 ∈ Int`, `1 / 3 ∈ Rat`: the calculator knows the
  sets `naturals`, `integers`, `rationals`, and the theories bind theirs (`calc Nat naturals`).
- arith.kurt: how `<`, `<=`, `>`, `>=` relate ("le-ge", "lt-gt", "lt-le", "le-refl", "lt-ne").
- `let x with P(x)` (the same as `let P(x)`, naming the constant) and `pick c > 0` (the same as
  `pick c with c > 0`): `let` and `pick` take conditions the same way. A `pick` without a matching
  `∃` suggests `let`.
- The shell fills in the indentation: each line starts with the one of the current block (one
  level deeper after `proof`, `assume`, ...), and a backspace dedents.
- `expect "KIND" "TEXT"`: the error message must also contain the text. The tests use it instead of
  the `;;; ` markers on the last line, which are gone.
- A `todo` inside a discarded block (`sandbox`, `expect`, `break`) no longer counts as open.
- `pick x with P(x, y)`: a comma inside brackets no longer splits the line.
- Instantiating a `∀` with a value that already occurs in the formula: the matcher now also tries
  some of the value's occurrences as the bound variable, not only one or all of them.
## 0.7.1 (2026-10-02)

### Fixed

- **A soundness bug:** a `let` constant counted as a variable again in a block inside the `let`
  block. So `let %E` / `assume %E` / `Q` was accepted -- the assumption read as "for every `%E`"
  -- and closing both blocks gave `%E implies Q`, from which `Q` followed: anything was provable.
  The kernel shared the mistake. Also, a `%`-name made a constant by `let` is boolean now.
  Regression test: `proofs/soundness/let-constant-stays-constant-in-nested-blocks.kurt`; see
  `doc/kurt-soundness.md` §8.18.

### New

- `scripts/kurt2lean.py`, a prototype that translates a checked proof into Lean 4 from its
  certificates, so that Lean's kernel checks it again (`python3 scripts/kurt2lean.py proof.kurt
  -o proof.lean && lean proof.lean`). It found the bug above. Numbers, `calc`, quantifiers with a
  condition and `def` aren't translated yet.
- `CITATION.cff`, for citing Kurt; the website www.kurt-lang.org; the release workflow can be run
  by hand for an existing tag.

## 0.7.0 (2026-10-02)

The first public release, after development since 2016. The language isn't frozen yet: a proof written for 0.7 may need small changes for 1.0.

### New

- **A kernel checks every step again.** Each step the search accepts comes with a certificate
  (which rule, which facts, which values), and a small checker verifies it without any search.
  This also covers closing blocks and `pick`. A step the kernel rejects is a `KernelError`,
  which no `expect` can catch. `cert N` shows the certificate of line `N`.
- **`.kurtc` files**: `kurt FILE.kurt` keeps the certificates of a completely checked file.
  The next run checks them with the kernel instead of searching. They are only hints: a
  changed file, or a certificate that doesn't check, just means searching again.
  `kurt --deps FILE.kurt` shows the tree of loaded files and whether their certificates are up
  to date, and `--no-kurtc` switches them off.
- **Each loaded file is checked on its own**, in a fresh context: only the core and what it
  loads itself. A library can't use its loader's facts, and the order of loads doesn't matter.
  Its exports must agree with the loader's symbols (the same declarations, the same `def`).
  Within a run, each library is checked once.
- `save "file.kurt"` writes the accepted lines of a file or a shell session, as Kurt source.
- Quantifiers and other binders with a condition, written in rules as `sub $x $v %C`, e.g.
  logic.kurt's "forall-cond-elim". There is a new theory, `analysis.kurt`: `abs`, finite sums,
  `max`/`min`, `sup`/`inf`, and limits by ε and δ, also with a condition.
- Tuples in set.kurt: `(a, b)`, "pair-eq", `fst`, `snd`, and `A × B`. The comma is
  right-associative, so `(a, b, c)` is `(a, (b, c))`. `f(a, b)` means `f a b`.
- `group.kurt`, with operator variables (`var ∘`, `infix ∘`) and operators as arguments:
  `group(R, (+), 0, (-))`.
- `calc`: theories bind their symbols to the built-in calculator (`calc + add, ...`), and
  numbers are exact (`0.1 + 0.2 = 0.3`, `1 / 3` stays a fraction). The calculator also works
  while a step is matched against a rule.
- `python -m kurt`, and a cookbook of recipes (`doc/kurt-cookbook.md`). New tutorial lessons:
  46-cert, 47-tuples, 48-groups.

### Changed (may need changes in existing proofs)

- `^` is right-associative and binds more tightly than the prefix `-`: `- 2 ^ 2` is `-4`, and
  `2 ^ 3 ^ 2` is `512`.
- arith.kurt: "pow-add" and "pow-mul" need a positive base (`$a > 0`), and `calc` doesn't
  compute `0 ^ 0`.
- `def` must be conservative: its left-hand side is the new symbol applied to distinct
  variables, and its right-hand side has no other variables. `def`, `load` and `chain` are not
  allowed inside proof blocks.
- A library must load what it uses itself (see "each loaded file is checked on its own").
- One `pick` per line. `save` writes only `.kurt` files, and works neither with `--strict` nor
  in a loaded file.
- `1.0` is the number `1`. set.kurt no longer declares `brackets [ ]`, which no fact used.
- The symbols of a theory that comes with Kurt can't be declared anew (`bool Nat`,
  `infix Nat 50 50`).

### Fixed

A targeted soundness review (September 2026) fixed every bug it found, each with a regression
test in `proofs/soundness/` or `tests/`. Among them:

- `def` wasn't conservative;
- the variables of assumptions and `let` conditions counted as "for all";
- `pick` witnesses could escape their block;
- set.kurt's separation didn't bind its variable, and its function extensionality was false;
- forged `.kurtc` files were accepted;
- several steps were accepted by the search but not by the kernel;
- lines that crashed Kurt instead of giving an error.

See `doc/kurt-soundness.md` §8.17.
