# Changelog

## 0.12.0 (2026-10-30)

**Breaking, for 0.11 to 0.12** (each one below too): `numbers.kurt` is `number.kurt` (`load number`); `integer.kurt`, `rational.kurt`,
`real.kurt` and `objects.kurt` are gone (`load natural` has what they had; the sets `Real`, `Int`, `Rat` are in `number.kurt`; `even`, `odd`, `∣`, `coprime`
are in `divisibility.kurt`, `{a, ..., c}` in `interval.kurt`); the declaration `bindop` is `binder`; the sum is empty for `a > b`; a `def` is
local to the block it is in (and may not be in its result). New: `kurt --share`/`--unshare`, `kurt --profile`, `∃ x, y P`, `var real x, y`, an equation
whose first line is a term, `nested` and `binder SYMBOL POWER`, the intervals, a fact with several conditioned `∀` in one line, the editors' heat map.


- A fact with two or three quantifiers that have conditions, `∀ x ∈ V ∀ y ∈ V P`, is used in one line: Kurt derives the instance for the first
  `∀` as a step of its own (`9a by forall-cond-elim(V2, 7)`) and then the line; before, each `∀` needed a line of yours. If a condition is not
  known, the message names it (`V2 has 2 quantifiers with conditions ... but b ∈ V is not known`). Reference §4.4, soundness §8.52.

- A term on its own line continues on the next line (todo 80): `(a + b) * c` and, indented, `= a * c + b * c` are one statement `(a + b) * c =
  a * c + b * c` -- the usual way to write an equation in two lines, with further lines `  = ...` as in a chain (only the relations of a `chain`
  continue a term). A term line that nothing continues is the same error as before, "must be a statement", at its own line (also with all errors
  and in the editors); the shell waits for the next line, so a pasted file works. Reference §6.2.

- `binder SYMBOL POWER` (`binder sum 65`): the binding power of the body of a binder; without it the body stays one tight argument.
  `nested forall, exists` (in logic.kurt) declares the binders whose variable may be a list, `forall x > 0, y > 0 P`: the quantifiers
  are no longer found by their engine roles. Reference §4.4. The theories use it: `forall`, `exists`, `existsunique` 17 (the comparisons
  and `not` inside, `and`, `or`, `implies` outside: `∀ x x > 0 ∧ x < 5` is `(∀ x (x > 0)) ∧ x < 5`), `sum`, `max`, `min`, `argmax`, `argmin`, `sup`,
  `inf`, `lim`, `integral`, `integrable` 65 (`*` inside, `+` outside: `sum i (1, n) i * 2 + 1` is `(sum i (1, n) (i * 2)) + 1`). Before, a body
  was one tight argument and such a line was a type error; no file of the corpus reads differently.
- The number files (plan step 6-8): **Breaking**, a file that loads `integer`, `rational` or `real` loads `natural` now (`Int`, `Rat`,
  `Real` are in `number.kurt`, which is `numbers.kurt` renamed: write `load number`); `even`, `odd`, `∣`, `coprime` are in
  `divisibility.kurt`; `{a, ..., c}` and the new intervals `Icc a b`, `Ico a b`, `Ioc a b`, `Ioo a b` in `interval.kurt` `objects.kurt` is gone (its sorts are in `set.kurt`).

- `kurt --profile FILE`: after the check, the ten slowest lines with their time and search steps; `RunConfig(profile=True)` fills
  `CheckResult.profile` (also in `--json`). The language server marks lines of 2 s or more (Information, and the time in the hint).

- **Breaking:** the declaration `bindop` is now `binder` (`binder forall`, `binder sum`): the common word, and the one the messages and the
  reference already used. No alias: a file of your own that says `bindop` says `binder` now (the theories of Kurt are changed). Also
  `keywords/32-bindop.kurt` is `keywords/32-binder.kurt`.

- `exists x, y, z P` (and `forall x, y P`) with several variables, each with its own condition if wanted (`forall x > 0, y > 0 P`): `exists x exists y exists z P` (`pick x, y, z with ...` is the proof side).

- `var real x, y, z` and `const real c, d`: a sort in front of the names declares them and gives them that sort (reference §3.2).
- Fixed: a `KernelError` for a stored fact `(C or (forall y %X)) implies G` used with "or-elim" (todo 76).

- **Breaking (analysis.kurt, todo 78):** the empty sum is 0 for every range with `a > b` ("sum-empty": `use $a > $b ⇒ sum i ($a, $b) T = 0`;
  before, only `sum i (b + 1, b) T = 0`), and "sum-last" has the premise `$a <= $b + 1`. The sum is no longer the signed one (for fewer
  than no terms its negative): with that, the rule for all ranges together with "sum-last" without a premise gave `3 = 0`. A proof
  that cites "sum-last" proves its premise (`0 <= k + 1`); `kurt --lean` writes `sum` as `if a ≤ b then ∑ n ∈ range (⌊b - a⌋₊ + 1), T (b - n) else 0`.

- doc/kurt-ref.md §8.2 starts "What gets exported" with a table (a `load` brings / stays in the file), also in
  keywords/17-local.kurt and tutorial/12. The reference said a `local` declaration that an exported fact needs
  "still goes along"; it is an error (as the spec says).

- The lessons write the bound variable of a quantifier as a plain name (`forall x P(x)`, `exists x > 0 P(x)`); the `$` is only for
  the free variables of a rule. Nothing changes in Kurt (`∀ $x` is still accepted); doc/kurt-ref.md §3.4 says so.

- **A `def` is allowed inside a block** (`proof`, `assume`, `case`, `let`, `pick`; todo 77), also with
  `--strict`. It is local to the block: the symbol is a constant of the block, it and its defining fact
  are gone when the block closes (a later block may define the name anew), and the block's result must
  not mention it (`ProofError: \`w\` is defined in this block ...`). Its right side may mention the
  block's constants: `let a`, then `def w = a * a + 1` names a witness that depends on `a`. The kernel
  checks the scope on its own, `kurt --lean` writes such a `def` as an `obtain` in the proof, and the
  hover says "local to its block". `use`, `chain`, `load`, `inline` and the grammar declarations stay
  refused in a block. Lesson tutorial/09a and keywords/12-def show it.

- A tutorial lesson on proving an existential statement: tutorial/09a-prove-an-existential-statement.kurt (the witness,
  `exists-intro`, a computed witness, a condition, two quantifiers, a witness from a `pick`, a wrong witness).

- numbers.kurt has the binomial formulas as proved theorems: "binomial-plus" `(a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2`,
  "binomial-minus" `(a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2`, "binomial-product" `(a + b) * (a - b) = a ^ 2 - b ^ 2`, and
  "two-times" `2 * x = x + x`; a step like `(x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2` follows from them in one step
  (proofs/arithmetic/binomial-formulas.kurt). They rest on one new rule, "pow-two" `$a ^ 2 = $a * $a` (for every base;
  in Lean `Real.rpow_two`, proved there like the other rules).

- numbers.kurt has a proved theorem, "squares-non-negative": `∀ $x ($x * $x >= 0)` (by trichotomy, from its rules). It loads
  `logic` now, for the quantifiers.

- `kurt --share FILE` prints the playground link of a proof (`#proof=`, the text in base64) and `kurt --unshare LINK` prints
  the proof of a link back, so a proof can be sent as a link and turned into a file from the command line; the Python
  for both is in doc/kurt-ref.md §1.

## 0.11.0 (2026-10-26)

- Two false rejections of the search, fixed (todo 50). A number or a string was taken for a clash with a
  `sub` term, so a rule whose conclusion keeps its `sub` was skipped: `(sum i (1, 1) i) = 1` after `load
  analysis` was rejected, though "sum-one" fits. And the search put the hole of `sub $x $a $T` into a `$T`
  that depends on no binder, which the kernel rightly refused (`P($a) ⇒ Q(sub $x $a $T)`, `use P(c)`, then
  `Q(c)`: a KernelError); now the hole is blocked as a range too.

- Speed (todo 50): a false goal after an n-way disjunction is refuted at once where the premises' parts
  cannot take their values together (`shared_case(8)` 7.4 s → 0.05 s), and a binder at the top of a premise
  is rigid there; the unifier is cheaper (`scripts/bench.py` 35 s → 29.5 s over the last rounds). What
  remains: a disjunction with one alternative twice (`A0 ∨ ... ∨ A7 ∨ A7`, 5.8 s at n = 8).

- Known limit (todo 76): with `load logic`, `use A or C or (forall z P(z))`, `use A implies G`, `use (C or (forall
  y %X)) implies G` and the goal `G` give a KernelError ("or-elim" binds `%X` in terms of the disjunction's
  bound variable); it is safe, only a rejection of a correct step.

- `kurt --latex` and `--markdown` no longer print the line a first use infers (`prop P 0`, "added statement
  places") as a row of the document (since 0.10.0 the reason was named differently than the filter expected).

- The messages and the documentation say "statement" (a statement place, a statement variable, an operator
  with a statement as its result) where they said "boolean": a statement is what is proved, no object of a
  sort (decision 17 of dev/todo-sorts.md). A second `prop` for a symbol says `already declared prop` (was
  `already declared bool`); e.g. `must be a statement` (was `must evaluate to boolean`), `a term as its result`
  (was `a non-boolean result`), `` `let` takes new constants or statements``.

- What a fact rests on, the leftovers (todo 64): the editors' hover of a theorem at the top level says it in
  one line ("rests on: 2 axioms of mine.kurt, 1 axiom of propositional.kurt, no todo"); `kurt --foundation
  LABEL FILE` shows one fact (by its label or line; `--foundation FILE` as before); an unlabelled top-level
  `use`, `def` or `todo` is an entry too, named by its line; a `calc` step names the file that bound its
  symbols (`` `+` add of numbers.kurt``, `bound_in` in the JSON).

- The symbols of Kurt's theories have ASCII names, words, and the Unicode symbol is their alias (todo 61):
  `union`/`∪`, `intersect`/`∩`, `emptyset`/`∅`, `subset`/`⊂`, `superset`/`⊃`, `notin`/`∉`, `cross`/`×`,
  `to`/`→` (set.kurt), `neq`/`≠`, `divides`/`∣`, `times`/`·` (field.kurt, matrix.kurt), `compose`/`∘`, and the
  connectives of lambda.kurt and modal.kurt (`lambda`, `reduces`, `steps`, `proves`; `imp`, `equiv`, `wedge`,
  `vee`, `neg`, `bot`, `box`, `diamond`) -- the table is in doc/kurt-ref.md §4.7. A file may write either; a line
  is printed with the symbols it was written with (`{}` now as `{}`, not as `∅`). **Breaking:** the words are
  symbols of the theories now, so a file that loads set.kurt and declares its own `union` (`subset`, `to`, ...)
  clashes with set.kurt's; the listings, the messages and the sort signatures name the words; the order of the
  arguments of a symmetric operator follows the words (`$a ∣ $b ∧ $a ∈ Nat`); `kurt --lean` names a symbol by
  its word (`subset`, `divides`, `times_d2`; was `k_u2282`, ...). A declaration written with an alias is about
  its symbol (`tex ∪ \sqcup` declares the LaTeX of `union`, `chain ⊂` is rejected as `chain subset`).

- CI tests Python 3.14 too (3.10, 3.12, 3.13, 3.14); the suite passed under 3.14.7 (todo 56).

- The reference is `doc/kurt-ref.md` (was `doc/kurt-doc.md`), also as a website generated from it
  (MkDocs: `scripts/build_reference_site.py`; at harmeling.github.io/kurt-web/reference/ with the
  playground). The README points to both at the top.

- A warning at the end of a file that declares a sort and names no object of it: all sorts are
  inhabited, so the file assumes one (`the sort `vec` ... has no constant in this file`).

- Overloading, stage 1: `+ - * /` have a signature on `real` and one on `complex` (`real ⊂ complex`), a term has
  the least sort of its arguments (`(1 + 2) < 3` is as well-sorted as before, `z + 1` is a `complex`); the kernel
  recomputes it (doc/kurt-kernel.md §8.5). New theories: complex.kurt (the sort `complex`, `i`, `Complex`/`ℂ`,
  the laws of a field, `re`, `im`, `conj`, `cabs`; `calc on` computes exactly with Gaussian rationals) and
  real.kurt (the number tower in one `load`).
- Complex numbers (todo 48): `^` overloaded on `complex` too, with the laws for a natural-number exponent
  ("complex-pow-succ"; `calc on` computes `(1 + i) ^ 2`); `kurt --lean` of complex.kurt and of a proof with complex
  numbers (Mathlib's `ℂ`, a real cast into it, an overloaded operator by the least sort of each occurrence,
  `lean complex ^ k_cpow $1 $2` for one profile; every rule of complex.kurt a theorem of Mathlib); `kurt --latex`
  writes `ℝ`, `ℂ`, ... as `\mathbb{R}`, ... (not Kurt's shortcuts `\R`, `\C`, which are no LaTeX), symbols in a
  reason in math, and `a + (-a)`, `a · (-1)` with brackets; `i` is `\mathrm{i}`. `abs` stays on `real`, the modulus
  is `cabs` (a result of another sort than the argument is stage 2 of overloading).
- Language server: `$/cancelRequest` stops the check of the request, and an edit during a check stops the check
  of the old text (a reader thread takes them while a check runs).
- Diagnostics: the sort-mismatch explanation names the sort of the value; a premise a rule needs over every
  object, that a fact states only over the numbers, is explained (`restriction_hint`).
- Speed: `operator_parameters` reads only new facts, `assume A ∧ B` tries "and-elim" first, `write_kurtc`
  serialises once -- mafi1/28-self-adjoint 17.0 -> 11.9 s, rational.kurt 10.7 -> 5.8 s.

- `qed` cites its proof: the proof's last line is tried first, before the rules of the loaded
  theories -- the reason follows the proof as written, and its lines no longer count as "not used"
  (propositional.kurt's "iff-true-elim" closed by a chain of two other rules before).
- Induction over a property that is itself a `∀` (todo 52): a goal `∀ s ∀ y R(s, y)` is matched also as a
  whole against the conclusion of an induction rule, so the property is `∀ y R(s, y)` and the induction
  hypothesis holds for every `y` (before, the property lost its inner `∀`s; the workaround was a `def`). The
  same makes a rule concluding `∀ $t %P` usable, not only `∀ $s (sub $t $s %P)`.
- Conditional rewriting in a chain about free variables (todo 52): the line before, which has its own names for
  the free variables, is compared with the next one under the same names -- `get (ins 0 B (ins c A Γ)) n = get
  (ins c A Γ) n` continued by `= get Γ n` with a conditional rule is found, without its instance as a line first.
- `let w with $a <= w ∧ ...` inside a block that fixes `$a` (todo 52): the fixed `$a` is no candidate for the
  new name (before: "expected exactly one new symbol or existing").
- proofs/classics/lambda-preservation.kurt without its three `def`s and four instance lines, the intermediate
  value theorem with `let ... with`.
- Speed (todo 50): a false goal after an n-way disjunction with its cases is no longer exponential in n (a split
  of the alternatives is tried only if the premises' groups can cover them exactly; n = 8: 14.6 -> 0.15 s, n = 32
  0.24 s); `cannot_unify` knows a `flat` operator with rigid arguments; the operator parameters from each
  fact's heads, the tops of the arguments before `cannot_unify` -- scripts/bench.py 44.1 -> 34.9 s
  (mafi1/28-self-adjoint 15.2 -> 10.9 s).

## 0.10.0 (2026-10-20)

**Breaking changes** -- a file written for 0.9 needs these edits:

- `bool` is `prop` (`prop A, B`, `prop even 0`), and `load prop` is `load propositional`.
- The number sort `num` is `real` (`real x`, `default real`); the sets of numbers are `Nat`, `Int`,
  `Rat`, `Real` (also `ℕ`, `ℤ`, `ℚ`, `ℝ`).
- A statement is no object (`c = (A ∧ B)`, `A ∈ M` are type errors; compare statements with `⇔`),
  and an operator is no object (`f = g` of two function symbols; a function as a value is a mapping
  of set.kurt).
- Binders and `let` range over terms: `∀ %A`, `let %A` are type errors -- a statement variable is
  schematic (`use %A ∨ ¬%A`), and a proof about `%A` needs no `let`.
- The first sorted use of a symbol is final; the core sort `term` is gone (a symbol without a sort
  is `any`); an unsorted binder ranges over all objects.

- `kurt --version` shows in three lines the version, the path of the `kurt.py` that runs and its
  SHA-256 (as the banner) -- so the editors' "Kurt: Show Version" says which Kurt runs.

- Fixed: a theory of Kurt opened in an editor (`propositional.kurt`, `set.kurt`) was checked as a
  stranger's text -- its roles and chains refused, also in every proof that loaded it while it was
  open. An editor's text at the path of a theory of the running Kurt, unchanged, is that theory now;
  a changed text stays untrusted.

- Fixed: a theory of Kurt opened by another spelling of its path (Kurt installed through a symbolic
  link, the editor naming the real path) counted as a file of the user's -- its roles and chains
  were refused. Paths are compared resolved now.

- The comma of a tuple takes terms: passing a relation `(R)` in a tuple no longer gives the comma a
  statement place (which made every later `(x, x)` a pair of statements); a statement in a tuple is
  a type error. A variable that the same formula applies as a relation (`R(x, x)`, `var R; prop R 0`)
  is an operator parameter, no statement.

- Binders range over terms: `∀ p (p ∨ ¬p)` with a statement `p`, or `∀ %A ...`, is a type error. A
  statement variable is schematic (`use %A ∨ ¬%A`: for every statement). `let` fixes a term only:
  `let %A` is a type error; a proof about `%A` needs no `let`.

- `bool` is now `prop` (`prop P`, `prop even 0`, `prop ∧ 0 1 2`), and the theory `prop.kurt` is
  `propositional.kurt`. `prop` declares statements and is no sort: `sort prop`, `sort any prop` are
  refused, `sort` doesn't list it. `%A` is called a statement variable. Lesson keywords/01-prop.kurt.

- A statement is no object: a statement at a term place (`c = (A ∧ B)`, `A ∈ M`, `f(A ∨ B)`) is a
  type error ("use `⇔`" to compare statements). Statements and terms are two categories; the first
  use of a new operator decides which of its places take statements, and that is final.

- Fixed: a binder whose condition has an `inline` operator bound the wrong variable (`∀ x >= y (P x)`
  with a new `y` bound `y`); the bound variable is the first symbol as written again. The classic
  theorems in `proofs/classics/` (todo 44): Cantor, infinitely many primes, the intermediate value
  theorem, Knaster-Tarski, preservation for a typed λ-calculus, Lagrange up to the counting.

- The number sort is `real` (was `num`): `real x`, `default real`, `lean real ℝ`; the convention
  "sorts lowercase, sets capitalized" (`real x` vs. `x ∈ Real`, doc/kurt-doc.md §5.2). "ext-num" is
  "ext-real". New lesson keywords/47-default.kurt.

- The set `Real` (`ℝ`) of all numbers and "ext-real" (natural.kurt): two sets of numbers with the same
  numbers are equal, for a `default real` file, where `∀ n` ranges over the numbers only; `Nat ⊂ Real`,
  `Int ⊂ Real`, `Rat ⊂ Real`, all proved in Lean. `ℕ ℤ ℚ ℝ` (`\N \Z \Q \R`) are aliases of `Nat Int Rat
  Real`. `kurt --lean`: a rule's own Lean proof gets the definitions it unfolds; a chain of `⇔` is
  proved (by `grind`) with numbers loaded.

- `kurt --lean`: a conjunct of a conjunction ("and-elim") is its projection by position (`h.2.2.1`),
  before any search; vectorspace.kurt's export, whose twelve conjuncts made `simp` run out of
  heartbeats, now checks in Lean.

- `default real` yields to the line: in `use A = {n ∈ Nat | n > 2}` a new constant `A` is a set (the
  sort of the other side of `=`), not a number equal to a set of numbers.

- Operators are no objects (doc/kurt-doc.md §5.3): `f = g` for two function symbols, `P(f)`, a
  quantifier instantiated with an operator are type errors; a function that is a value is a mapping
  of set.kurt (`f ∈ A → B`, "function-extensionality", proofs/set-theory/function-extensionality.kurt).
  An operator is passed only to an operator parameter of a defined predicate: group.kurt's inverse is
  the operator variable `ι` now, `group(R, (+), 0, (-))` as before.

- Sorts are order-sorted logic, with five rules (doc/kurt-doc.md §5.2, the tutorial's lesson 29;
  why it is sound: doc/kurt-soundness.md §10, doc/kurt-kernel.md §8): the sorts form a hierarchy
  with `any` on top (`real ⊂ set ⊂ any`); every symbol without a sort is `any`, and a constant gets
  its sort at its first sorted use, which is final (no narrowing: a later use at a smaller sort is a
  type error that says what to declare); a value fits a place of its sort or a bigger one; `∀ x` and
  `∃ x` range over the sort of `x` (without one over all objects, inside a formula as at its top, so
  a student's `∀ x` meets extensionality); a rule for every sort writes `$$x`, and one use of it is at
  one sort (before, "existsunique-intro" over `any` and `real` at once proved `false`). `any` is a
  core sort (`any x` declares a symbol of all objects); `default any` is the same as no default, the
  theories and files that had it don't any more. The meet of two sorts is their greatest common
  subsort. A type error for a symbol that a fact puts in a set says that a fact gives no sort.
  Removed: the core sort `term` (it was unsound with the first sorted use; `lambda.kurt`'s sort is
  `term` again) and the declaration of the sort of a set's elements (`real ∈ Nat`, `set ∈ Pow`, `set
  ∈ →`: a proof that needs `c ∈ Pow(A)` as a set says `set c`). A sort signature after a symbol
  occurs in a fact is refused.

- A polymorphic rule (`$$x`) rewrites under a `∀` over any sort: "forall-iff" and the other rules
  with a `∀` premise were used only for binders without a sort; the search and the kernel now let
  the rule's binder stand for the goal's binder over `set`, `real` or `any`.

- Polymorphic variables `$$x` (todo 35): a rule that holds for every sort writes its bound variable
  `$$x` (logic.kurt's quantifier rules, "separation"); the search and the kernel check that it
  occurs only in its binder, in `sub`s and as a side of `=`. This replaces the rule the search
  computed (a binder that happened to occur only there was used for any smaller sort). `real ∈ Nat`
  (the sort of a set's elements) is dropped: a sort never comes from a fact; induction needs the
  variable to be a number (`default real`).

- `kurt --lean`: sets and numbers in one model -- the objects are Mathlib's ZF sets, the numbers
  the reals, embedded into them by a definition (no axiom); every rule of set.kurt and natural.kurt's
  notations `{a, ..., c}`, `{a, b, ...}` are theorems; the logical theories' rules are generic
  over the type, so they apply to numbers and to sets; `lean SORT TYPE` (`lean real ℝ`) gives a
  sort its Lean type. Of 96 example proofs Lean checks 91 completely (before 89).
- Sorts with subsorts (`sort set real int`: `int ⊂ real ⊂ set`, read like `chain`), `default SORT`
  per file, inference of a symbol's sort from its first sorted use in every file (the default
  decides where a use allows several sorts), `everything set` (the sort of all objects), and `real ∈
  Nat` (the sort of a set's elements). A number fits where a set is required, a set is no number
  (`{1, 2} + 0` is a type error); the type checker, the search and the kernel check it. The line
  output and the hover say how a symbol got its sort. New theory objects.kurt; numbers, natural,
  integer, rational and analysis are sorted (`default real`), set.kurt has `default set` and the
  rule "separation-in". doc/kurt-soundness.md §8.41: why extensionality needs elements of every sort.
- `~/.kurt_history` is written only when the shell added to it: `kurt FILE`, piped input and
  `--json` rewrote it at every exit (truncated, converted from libedit's format; a shell open
  meanwhile lost its lines).
- A type error says how the line was read, as part of the error ("the line was read as `not P`"):
  the "parsed as: ..." went straight to stderr, outside `check_text`, `--json` and the editors.
- `def` of an operator declared `sym` or `flat` says so (it said "remove its `const`", which
  nobody wrote: `sym`/`flat` make the operator a constant).
- `kurt --lean`: the rules of propositional.kurt, logic.kurt and equality.kurt are theorems of Lean's logic
  (`lean "label" grind`, no Mathlib needed), `∃!` and `invimplies` by their `lean` templates; a
  `def` over a tuple (`def coprime($a, $b)`) is a Lean function of two arguments, and the `def`s of
  what a proof cites are Lean `def`s, so natural.kurt's theorems about `even`, `odd`, `∣`,
  `coprime` and `⊂`, and rational.kurt's "lowest-terms", are proved in Lean; a numeral without a
  number theory is a constant of its own (field.kurt's 0 and 1, peano's numerals). Lean checks all
  72 example proofs completely (before 60); 219 of the theories' 226 rules are Lean theorems.
- Tests: an audit of the test code (39 bugs). About 20 tests that couldn't fail now fail on the
  behaviour they guard (the load cache, `info`, exported schemas, strict declarations, the shell's
  history, the parser's later expressions, n-ary case certificates, the alias cycle, the export of
  labels over `load`, the pick-witness leak, the `def` with a bound variable, the syntax of all 19
  theories over `load`); expected errors are pinned to their texts where the file promises a
  message; no test writes into tests/ or /tmp/.kurt_history or leaves files in /tmp any more;
  budgets of 3 s for cold processes; the shell test waits for its prompts.
  `scripts/publish-public.sh` accepts a public checkout that is a git worktree.
- Fixed: on macOS, a file's steps were taken for another file's -- `kurt --lean` wrote no
  theorem, the hover of a `load` linked a wrong path, a `.kurtc` was refused. Since 2026-10-15 a
  loaded file was named by its path with symlinks resolved, and macOS's temporary directory `/var`
  is a symlink to `/private/var`. A file keeps the name it is found by now; only whether it is
  loaded already compares resolved paths (`same_file`), so a file through a symlink still counts
  once. The CI job `macos` had failed since then.
- `kurt --lean` with Mathlib: the theories' rules are theorems that Lean proves -- a rule's proof
  is kept with it, `lean "label" TACTIC` (raw to the end of the line; only output, Kurt never reads
  it), and the export writes it as a `theorem`. All number theories are ℝ now (`Nat`, `Int`, `Rat`
  its subsets, `lean Nat member ...`; `n!` is Γ(n + 1)); binders have `lean` templates (`lim`,
  `sum`, `deriv`, `integral`, ...). 187 of the 194 rules of numbers, natural, integer, rational,
  analysis, continuity, sequences, derivative and integral are proved (not: the definitions of
  `{a, ..., c}` and `{a, b, ...}`, and "integral-riemann", which isn't in Mathlib); the 15 example
  proofs about numbers rest on 6 axioms of these theories (before 48). No rule was false.
- `kurt --lean` with Mathlib: a theory declares how its symbols read in Lean (`lean + $1 + $2`,
  `lean Obj ℝ`); a proof about numbers is exported with `import Mathlib`, its numerals and `calc`
  steps (`norm_num`) translated. numbers.kurt and analysis.kurt are ℝ, natural.kurt ℕ, integer.kurt
  ℤ, rational.kurt ℚ. The lake project scripts/lean and scripts/lean_check.py check an export (not
  part of the package: Kurt needs neither Lean nor Mathlib). Of 72 example proofs, Lean checks 60
  completely (before 48), none with errors.
- A boolean operator without its arguments where a statement is required is a type error: `¬ P`
  with `arity P 2`, `A ∧ (=)`, `P ⇔ Q` for two predicates -- with a hint how to apply it ("apply it
  to its 2 arguments, e.g. `P a b`", "write it between its arguments, e.g. `a = b`"). Before, such
  lines were accepted. The type check also looks inside an operator that is itself an expression
  (`(¬¬P) c c`). proofs/errors/bare-operator-as-statement.kurt.
- Soundness: the hole of a `sub` is never cut at an operator position, and a bare operator (`=`,
  `∧`, a `prop P` of arity 2) is no formula -- in the search (`hole_nodes`, `bare_operator_for`)
  and in the kernel (`k_is_statement`, `k_has_kind`); "iff-subst" had given `R (c = c)` from
  `R ((¬¬(=)) c c)` with `%b := =` (soundness §8.40, proofs/soundness/hole-never-at-an-operator.kurt).
  Operator variables (`var ∘`) are unaffected. The hole may still be cut at an operator that
  yields a term (`term_operator`): `f = g` rewrites `f a` in one step, `P ⇔ Q` doesn't rewrite
  `P a` (doc/kurt-doc.md §8.1, "Where the hole of `sub` may be", with both examples).
- Fixed (soundness): a `$`-variable of a fact could take a formula as its value through
  "iff-subst": the hole of `sub` was cut at an operator (`=` of `c = c`), and the value `(¬¬=) c c`
  was not recognized as a formula. Now a node with a compound operator has the kind of its
  operator, and the kernel checks that every value has the kind of its variable
  (`k_is_statement`; doc/kurt-soundness.md §8.39, proofs/soundness/term-variable-takes-no-formula.kurt).
- `load` with up-to-date `.kurtc` files is faster: the theories that come with Kurt are looked up
  once (the directory was listed on every lookup), a theory taken from the cache shares its
  formulas instead of copying them, and a chain line replays with the steps it cites (`17a`) --
  before, every chain line was searched again despite its certificate. `load rational` 1.3 → 0.8 s,
  field.kurt and vectorspace.kurt 2.7-3.0 → 0.5 s.
- `kurt --lean`: quantifiers with a condition (`∀ x ∈ A P` as `∀ x, x ∈ A → P`), every other
  binder as a higher-order constant (`∃!`, `sum`, the set-builder), `def` as a Lean `def` with its
  equation by `rfl`, `flat`/`sym` as associativity/commutativity axioms, `case` steps, and a symbol
  used as a function and as an object (`f a`, `f ∈ (A → B)`) as an `Obj` with `k_apply`; a step that
  can't be translated is a `sorry`, never an error. Of 71 example proofs Lean checks 48 completely
  (before 38), none with errors (before 7); what remains is numbers.
- `kurt --foundation FILE`: what each top-level fact rests on -- its class (axiom, definition,
  todo, theorem) and the axioms, definitions, `todo`s and calculator steps behind its proof, by
  file, with the reverse index (each postulate, the facts resting on it); `check_file(path,
  foundation=True)` fills `CheckResult.foundations`, `result.foundation(label)`, `kurt --json`
  includes them. A `Reason` of a step carries its certificates (`Reason.certificates`); a `qed`
  admitted by a bare `todo` has a `todo` certificate.
- Search budgets: `kurt --budget SECONDS`, `RunConfig(time_limit=..., step_limit=..., cancel=...)`;
  a line whose search runs out of budget fails with a `ResourceError` -- a kind of its own,
  neither proved nor refuted, which `expect` can't name; `--all-errors` goes on after it.
  `CheckResult.exhausted`/`.cancelled`, also in `--json`. The language server allows 30 s of
  search per line (initialization option `budget`, 0 for none) and stops the check of a text that
  was edited meanwhile; `scripts/grade_exercise.py --budget SECONDS` (30 by default) reports an
  undecided line apart from a rejection. `scripts/bench_sessions.py`: the time of a cold `load
  rational` (8.2 s), with the shipped certificates (1.6 s), and again in the same session (0.09 s).
- The semantic oracle covers the first-order theories: `tests/test_first_order_semantics.py`
  checks all 13 rules of logic.kurt, both of equality.kurt, propositional.kurt's "iff-subst" (propositional.kurt is
  complete now) and all 23 statements of set.kurt in small finite models -- domains of 1 to 5
  elements, transitive universes of 5, 10 and 21 hereditarily finite sets with Kuratowski pairs --
  in every interpretation (all assignments, all tables of the schema variables, read with the
  proviso of doc §4.4), apart from the search and the kernel. All hold (doc/kurt-soundness.md
  §8.25, dev/dev-notes.md 2026-10-16).
- A named-goal grading API: `CheckResult.proves(statement, label)` says whether a file proves a
  statement at its top level -- derived there by steps that rest on no `todo` or error, not a
  `use`, not loaded, not withdrawn; `proof_of` says how it stands ('proved', 'admitted',
  'assumed', 'loaded', None), `loaded` lists the files a check loaded (also in `--json`). The
  statement is compared as Kurt reads it (`A ⇒ B` is `A implies B`). `scripts/grade_exercise.py`
  reports each `show` of the exercise as proved / admitted / missing (labels kept, notation and
  order free), refuses a file the exercise doesn't load, and runs with all errors; the textual
  comparison of lines is gone.
- Speed of the search: a plain symbol has its own bucket in the index of the theory, and
  `cannot_unify` looks below `=`/`⇔` and refuses a symbol against a term; `sub_solutions` and
  `guided_rewrite` skip what can't match. `scripts/bench.py` 50.6 → 35.0 s; n `case` blocks with n
  rules for the goal no longer grow cubically (`scripts/bench_case.py`, n = 64: 3.4 → 0.6 s,
  n = 128: 1.1 s). Every proof checks as before, with the same reasons.
- A claim that fails and is propositional (the core and propositional.kurt's connectives over statements)
  gets a counterexample in its explanation when there is one: an assignment of the atoms under
  which every fact holds and the claim doesn't, found by truth table (at most 12 atoms), checked
  again independently -- in the error text, `CheckResult.failure['counterexample']`, `--json` and
  the LSP diagnostics. Where the facts can't be evaluated (quantifiers, object variables: logic.kurt
  and everything on it) nothing is said: never a verdict from a search that found nothing
  (`propositional_counterexample`, `truth_value`).
- `doc/kurt-spec.md`: the logic of Kurt, specified (short, normative): terms and normal forms,
  the three kinds of variables (schematic, fixed, bound) and when an instance may depend on a
  bound variable, binders and their conditions, the step relation, the block rules of natural
  deduction, which `def` forms are conservative and why, `chain` and `calc`, `load` and the export
  bundle, trust and `--strict`, the kernel. Linked from `doc/kurt-doc.md`, README.md and CLAUDE.md.
- doc/kurt-kernel-code.md: the kernel read as code, in the Knuth sense -- each chunk of
  `kernel_verify`, `kernel_verify_block`, the `k_*` helpers, `Certificate` and `KernelEnv` is cited
  from kurt.py (`scripts/kernel_doc.py`, by `<!-- cite: ... -->` directives) and explained; a test
  fails when a chunk no longer is the code (`tests/test_kernel_literate.py`).
- `info SYMBOL`: prints everything known about one symbol -- its declarations, its `def` (if
  any), and the retained facts that mention it -- regardless of a loaded file sharing its name
  (unlike `list`, whose SOURCE is always a file).
- Fixed: an `expect "KIND"` block whose content finished without raising `KIND` left the shell
  stuck at the block's indentation, re-raising the same `ExpectationError` on every later line
  for the rest of the session. The block is now discarded (like a `confirmed` expect, or a
  `sandbox`) before the error is reported.
- Fixed: `kurt --lean FILE` silently produced an empty translation under a symlinked working
  directory (e.g. macOS's `/tmp` -> `/private/tmp`), since `export_lean` compared an `abspath`'d
  but unresolved path against the resolved path Kurt records elsewhere.
- A grammar declaration (`infix`, `prefix`, `postfix`, `brackets`, `arity`, `bindop`, `flat`,
  `sym`, `alias`, `sort`) is rejected inside `assume`/`case`/`let`/`pick`/`proof`, the same way
  `use`/`load`/`def`/`chain`/`inline` already were: its notation was never actually scoped to the
  block (a formula that survives the block locks in any declaration it needs, permanently) --
  `block_forbidding_declaration`, doc/kurt-doc.md §11.2.

## 0.9.0 (2026-10-15)

A change of the language (dev/design-sets-and-brackets.md, §10):

- Round brackets around a list are a tuple, a term of its own: `(a, b)` a pair, `(a, b, c)` a
  triple, `(a, (b, c))` a pair whose second component is a pair (before: the comma was
  right-associative, and `(a, b, c)` was `(a, (b, c))`); `{(a, b)}` is no longer `{a, b}`.
  set.kurt: "triple-eq".
- `f(a, b)` is `f` applied to one argument, the pair -- never `f a b` (before: `f a b` for an `f`
  of arity 2). `arity` takes the shape of the arguments, written as they are used:
  `arity g (_, _)`, `arity sum _ (_, _) _`; Kurt checks each use. The theories and examples are
  changed accordingly (group.kurt, natural.kurt's `coprime`, the exercises' scenes, ...).
- `def f($x, $y) = ...` defines `f` on pairs by their components (tuples are free).
- Sets by their elements: `{a}`, `{a, b, c}` -- set.kurt's `builtin { } setbrackets, | setbuilder`,
  `builtin ∅ emptyset` make three kinds of terms, by the elements, the set-builder `{x ∈ A | P}`,
  and `{}` (which is `∅`), so that set.kurt's new "singleton" never reads a set-builder or a list
  as one element. For each listed set, Kurt adds its rules (kernel-checked): an element is one in
  one step, membership is the disjunction of the equalities, and `case` splits it.
- `...` in sets of numbers (natural.kurt): `{1, ..., n}`, `{1, 3, ..., 99}`, `{0, 2, ...}`
  ("range", "progression", ...); a list whose pattern would be a guess, `{2, 3, 5, 7, 11, ...}`,
  is refused.
- `assume A ∧ B` (and `case`, `pick ... with A ∧ B`): the parts are facts too, shown as `6a`, `6b`.
- `pick` also takes its witness from an `∃` that follows in one step (shown as a line `13a`).
- Names may end in primes, `a'`, `f''`; a Greek letter may have digits, `λ1`. `~` and the symbols
  `∼` (`\sim`), `≈` (`\approx`), `≺` (`\prec`), `≼` (`\preceq`) for relations; `$R(x, x)` says how
  to write a relation as a parameter (`var R`, `bool R 0`).
- `format` without an argument also names the other options.
- The first line of a chain rewrites inside its left side as the later lines do (`L = L` as the line
  before it), also with a rule that has a condition.
- A line may rewrite up to four places at once; Kurt shows the steps in between (`17a`, ...).
- A rewrite may change a part of the arguments of a flat operator (`x + (- x)` inside a longer
  sum; for a non-`sym` operator, neighbours). field.kurt: `+` is `flat` and `sym`, `·` is `flat`
  (not `sym`: it is mafi1's matrix product too) -- the regrouping lines in field.kurt,
  vectorspace.kurt and mafi1 are gone; bench.py 60.6 s (68.5 s).
- A `let` whose condition is a set-builder closes (`let c ∈ { y ∈ A | P(y) }`).
- `inline` over a tuple: `inline child($x, $y) iff parent($y, $x)` (the scene of 02-family-tree);
  doc/kurt-doc.md §6.2 and keywords/46-inline.kurt: why not every `def` is an `inline`.
- A long disjunction is found at once (20 alternatives took more than a minute): a part of a
  pattern of a flat `sym` operator with a fixed head, like `¬%A` in "excluded-middle", is matched
  to one argument first instead of trying every grouping. bench.py 49.8 s (60.6 s).
- `inline`: a definition applied while reading -- `inline $a > $b iff $b < $a` reads `x > 0` as
  `0 < x`, one term, so nothing is to be switched. numbers.kurt: `>`, `>=` (no longer bound to the
  calculator: there is nothing left to compute); equality.kurt: `≠` (its rules "not-equal",
  "not-equal-intro", "not-equal-elim" are gone, `calc on` proves `¬(2 = 3)`); set.kurt: `⊃` (was a
  `def`, "superset"), and the new `∉`.
- `calc on` justifies a step instead of changing the line: a line is stored as written, and it
  follows computed (as before) or as written -- an instance of a rule stays one (`1 * (1 + n)`),
  `∃ k (7 = 1 + k)` finds `7 = 1 + 6`. `calc on` ends with its block (it stayed on after `qed`).
- A failed step names the missing condition of a fact `∀ y ∈ A (...)` ("line 3: missing `x ∈ A`");
  rules that fit almost any goal ("bottom-elim", "extensionality", ...) are listed only without
  others.
- set.kurt: "nonempty-element", "element-nonempty" (`U ≠ ∅ ⇔ ∃ x (x ∈ U)`), "subset-cond"
  (`A ⊂ B ⇔ ∀ c ∈ A (c ∈ B)`); vectorspace.kurt: "vector-minus-zero", "vectorspace-intro" (the
  definition the other way, so a subspace is a vector space). proofs/mafi1: `{0}` (10, 24, 26), the
  one-sided inverse of a matrix and (Aᵀ)⁻¹ = (A⁻¹)ᵀ (15).
- `kurt --latex FILE`, `kurt --markdown FILE`: the checked file as a document (`FILE.tex`,
  `FILE.md`), each line in mathematical notation with its reason, and the certificates; how a
  symbol is written is declared in its theory, `tex sum \sum_{$1=$2}^{$3} $4` (the theories that
  come with Kurt have them). `kurt --lean FILE` writes `FILE.lean`. They replace
  scripts/kurt2latex.py and scripts/kurt2lean.py.
- `arity sum _ (_, _) _`, `arity integral _ (_, _) _`: the range is checked to be a pair.
- Limits, sequences and series: analysis.kurt `tends v a L T` (the limit exists and is `L`), with
  the limit laws; continuity.kurt "cont-tends"; the new sequences.kurt: `converges n L T`,
  `seqlim n T`, the limit laws, "archimedes", series `series i a T` and the geometric series.
  Examples in proofs/analysis/ (1/n → 0 by ε and N, limit laws, 1 + 1/2 + 1/4 + ... = 2).
- continuity.kurt: only the definitions of `cont`, `diff`, `deriv` (derivative.kurt loads it);
  exercise 2 of 09-calculus asks `cont x 3 (2 * x + 1)` directly, by the definition.
- The matching of a symmetric operator with as many patterns as arguments stops a branch as soon
  as a pattern fits no remaining argument (it went through all n! orders).
- A symbol without arity is curried: `(g a) b` is `g a b`.
- New symbols: `∖` (`\setminus`), `∁` (`\complement`), `⟂` (`\perp`), `∋` (`\ni`), `⁻¹` (`\inv`).
- The standard LaTeX names as shortcuts too: `\le`, `\ge`, `\ne`, `\lnot`, `\land`, `\wedge`,
  `\lor`, `\vee`, `\Rightarrow`, `\Leftrightarrow`, `\bot` (what Kurt writes keeps its own).
- The error of an argument of the wrong shape shows a compound argument in brackets: "got `mysum
  i 1 (i * i)`" (was `mysum i 1 i * i`).
- `kurt --latex/--markdown/--lean FILE -o OUT`: the document to `OUT` instead of next to the file,
  `-o -` to the standard output (`kurt --lean p.kurt -o - | lean --stdin`); then nothing of a
  proof that doesn't check.
- `--latex`, `--markdown`: a line continuing a chain is `= x`, without the repeated left side; the
  document of a proof that doesn't check keeps the theories' notation (it had none).
- doc/kurt-kernel.md: the kernel step by step -- certificates, what it checks, `.kurtc`, what is trusted, with examples and diagrams.
- The lines of a proof that nothing cites are greyed out in the editors (an LSP hint with the tag
  "unnecessary"), and `kurt --unused FILE` names them: backwards from the top-level lines, the
  labelled ones and `qed`, along what each step cites -- a block whose result nothing needs is
  greyed out entirely. A line that restates a block's result, an assumption or the line before it
  isn't (the hover says that Kurt doesn't need it); `unused_lines`. A line continuing a chain
  (`  ⇔ C`) cites the chain's first line, where its left side comes from (the event's `chain`): when
  the last line of a chain is found directly, the middle lines are greyed out, the first isn't.
- The hover of the editors for every line that isn't a comment: a declaration, a toggle or an
  inspection says what it does, with its symbols (`var a, b`, `infix ^ 75 74`, `arity g (_, _)`,
  `calc on`, `tex`, ...).
- The shell edits its lines itself, the same on macOS, Linux and Windows, without `readline`
  (`LineEditor`, `Terminal`): the line starts with the indentation of the block, also on macOS
  (libedit couldn't), a backspace over it dedents; ←/→, Home/End, Delete, Ctrl-A/E/K/U/W, the
  history with ↑/↓ and Ctrl-R (`~/.kurt_history`, also one libedit wrote), Tab (a second Tab
  lists the possibilities), Ctrl-C drops the line, Ctrl-D ends; long lines wrap, pasted lines are
  read one after the other. Not at a terminal: plain lines. Windows (`msvcrt`): not tried yet.
- `break` gives up the innermost open thing: in the `proof` of a `show`, only the `proof` -- the
  claim stays open for a new `proof` (the shell says so); right after the `show`, or after that
  `break`, it withdraws the claim (`break`, `break`). Before, the first `break` withdrew the claim
  too. keywords/22-break.kurt. A withdrawn claim is a `todo` ("Proof almost checked"; the grader
  counted a file of `show X`, `break` lines as complete).
- A declaration at the top level of a file is exported with all that is known about the symbol
  (`const pi`, `infix ++ 50 50`, `arity g (_, _)`, `tex`, ...) -- before, a symbol crossed `load`
  only with an exported fact (`pi` "not declared" with `--strict`, `1 ++ 2` "never declared").
  `local` at the end keeps it inside (`const helper local`); not `var`, not in a block, not the
  constants Kurt adds by itself.
- Soundness: `calc on` computed `3 ∉ S` for any set `S` (only for the calculator's sets now:
  `Nat`, `Int`, ...); with matrix.kurt, `calc` made `0 · y` the number `0` though `y` may be a
  matrix (`[0, 0] = [[0], [0]]` followed); an `alias` before a `load` gave a theory's symbol
  another meaning (`alias false true`, then `load prop`) -- now an error. All three also with
  `--strict` (doc/kurt-soundness.md §8.34-8.36).
- Soundness: `...` was matched as an element of a range (`$y2 ∈ {$y1, $y2, $y3}` with `{1, ..., 3}`),
  and `false` followed; now no variable takes `...` as its value, also in the kernel (§8.37).
- The kernel checks that the fresh names of a `∀` premise are fresh (only the search's own
  `$$07`, once, not fixed by a block, not in the goal or a fact): a certificate that stripped
  `∀ y P(y)` with a constant was accepted (doc/kurt-soundness.md §8.33; never made by the search).
- `load`: a loaded file can't `alias` a symbol the loader knows (`const foo` here, `alias foo bar`
  there made the loader's facts about `foo` ones about `bar`, the mirror image of the `alias`
  before `load` above; doc/kurt-soundness.md §8.38); `const q local` that an exported fact needs is
  refused like a local `def`; `lib/../lib/x` and `lib/x` are one file.
- A chain continued with `>` or `>=` works (`a > b`, `  > c`): the chain is about the line as
  written, not about the `b < a` that `inline` reads it as ("invalid chain of operators `[<, >]`"
  before; and `a > b`, `  = c` claimed `a > c` without reading `>`).
- The editor (`kurt --lsp`) shares its cache of checked theories among its checks: the second check
  of a file didn't know the cached theory's dependent variables and sorts, so a clean file showed
  errors after a save (argmax.kurt), or the check crashed (gauss.kurt). What a run knows about a
  theory's variables travels with the `ExportBundle` now, and a bundle of another run is used only
  if its variable names are new in this run.
- No Python traceback for: a `.kurtc` nested too deep, a binary or unreadable file (also a `load`ed
  one), `-o` to a place that can't be written, `save 42`, the line editor's Ctrl-R search once the
  query matches nothing, a malformed message to `--lsp`, a user label `"enumeration"` (and
  `"element-1-of-2"` no longer suppresses the rules of a pair), `--latex`/`--markdown` of a file
  with the listing of `theory`, `infix`, `cert`, ... (26 shipped files), `--lean` of a file without
  a step at its top level.
- `a ≠ b ≠ c` on one line is `a ≠ b ∧ b ≠ c` (`≠` is a relation, `bool ≠ 0`; before it was read as
  `not ((not (a = b)) = c)`). `pick c with F` finds a derived `∃` of natural.kurt's "range" (its parts in
  another order, `k + -3` for the written `-3 + k`). A block is numbered from
  the line that opened it (`let x` without a condition: `4-5`, not `5`). A line only admitted
  (`todo F`, or a failed line with `--all-errors`) is cited as `5 (todo)`. `help use` explains that
  keyword. A `use` that only relates declared variables (`var a, b`, `use a <= b`) warns: it holds
  for every value of them. A constant used in a term can't become a statement later; `def c = (a =
  a)` is a type error; the right side of an `inline` counts as a use of its symbols; `bool Nat` here
  and `const Nat` in a loaded file is an error (and the other way round). A multi-place rewrite shows
  only the step it uses, and follows at most six partial rewrites by a search (a false `5 ∈ {1, ...,
  3}` took 36 s, now 16). The grader (`scripts/grade_exercise.py`) searches only the scene and
  Kurt's theories for `load`, not the directory it runs in (`RunConfig.search_cwd`).
- A false membership in a set of numbers took long (`5 ∈ {1, ..., 3}` 36 s, `1 ∈ {-1, 2}` 81 s after
  a set of three was used): the multi-place rewrite took the generated schema `$y2 ∈ {$y1, $y2}`
  as a base and tried to rewrite its variables into numbers, and a numeral into another. A place
  with a variable, with `...`, or with two numbers of different values is never rewritten now
  (`cannot_be_rewritten`); both take 6 s, the general search.
- `load prop numbers` loaded `numbers` only (`prop` was dropped silently): now an error that says
  `load prop, numbers`. The same file through a symlink is one file. `kurt notes.txt` checks that
  file (a `load` still adds `.kurt`). `python3 -m kurt.kurt FILE` without a RuntimeWarning (the
  package imports Kurt when first used). The hover of a `load` line links the files it loads.
  doc/kurt-doc.md §3.2 says how Kurt handles variables (`$x`, `var`, `let $x`, across `load`) and
  why `var` stays.
- derivative.kurt's "diff-pow", "deriv-pow" need `0 < $n`, sequences.kurt's "geometric" `$q ≠ 0`:
  with `$n = 0`, `$q = 0` they decided `0 ^ 0 = 1`, which numbers.kurt leaves open
  (proofs/soundness/pow-zero-stays-open.kurt). With matrix literals, an operator bound to
  `multiply` can't be `sym` (the factors would be sorted). Exercise 09-calculus/2's scene
  (definitions.kurt) writes out the three definitions instead of loading continuity.kurt, so the
  limit rules give no shortcut; exercises/08-limits/theory/sequences.kurt is `limits.kurt`.
- `chain` with `--strict` (it was refused there): it generates no rules -- each of the n² rules it
  stands for (`($a Ri $b) ∧ ($b Rj $c) ⇒ ($a Rk $c)`, the later relation absorbing the earlier)
  must be proved before it, and the error lists the missing ones as `show` lines; its notation
  then uses the proved facts. A chain has at most three operators (everywhere).
- VS Code (kurt-syntax): `kurt.reasons.column` is `"auto"` by default -- the reasons two columns
  after the 95th percentile of the widths of the lines with a reason, at least 20.
- Output: empty brackets as written (`[] = []`, was `[$$$] = [$$$]`); `cert` names a `case` block
  by its keyword (was `assume B`); `--latex` writes `R(x, x)` with the tuple's brackets only once;
  a closed `sandbox` is numbered by its lines (at the end of a file it said "5 closed" for 4
  lines); `summary` without a trailing space.
- The banner says what its hash is: `This is Kurt, v0.8.3 (...), 955dc8f61f77 (SHA-256 of
  kurt.py)` (was `file 955dc8f61f77`); the README says how to check it.
- The editors: a theory of Kurt that was only open in the editor (e.g. equality.kurt, opened to
  read it) counted as unsaved text, which is never trusted -- `load equality` failed with "the
  role `equality` of the engine can only be given by a theory that comes with Kurt". Now only a
  text that differs from its file counts as unsaved (and the message says so). An error in a
  loaded file is shown at the line of its `load` ("in equality.kurt, line 14: ..."), not at its
  own line number in the file being checked; `error_line` (`--json`, `CheckResult`) is that line.
- The editors (`kurt --lsp`): the hover over a line that prints something besides a reason --
  `builtin`, `infix`, `arity`, `theory`, `load` without arguments, `cert 14`, ... -- shows that
  output (its first 60 lines).
- The theories come with their certificates (`.kurtc`; in the package next to them, in the
  single-file `kurt.py` embedded, made by `scripts/build_certificates.py`): `load rational` in the
  single-file `kurt.py` (and the playground) took 8 s each time, now 1.2 s. A theory's
  certificates name it `<kurt>/rational.kurt`, not by its place; where its directory isn't
  writable, they go to `~/.cache/kurt`. An unchanged `.kurtc` isn't written again (0.5 s). The
  files loaded by `check_text` use their certificates too (only the text has none).
- A line with certificates, none of them for the line as a whole (a step of a chain that rewrites
  a part): the search was the slow one, without its order of facts and rules -- `load field` with
  its `.kurtc` took 15 s, without it 7 s; now 4.5 s.
- `builtin [ ] matrixbrackets` (was `builtin [ matrix`): a role of a bracket pair takes both
  brackets of a declared pair.

## 0.8.3 (2026-10-11)

- Fixed a soundness bug: a derived fact `∀ c ((Q x 0 c) = (Q x 1 c))` (from a `let c`) could be
  used with `c := x`, the bound variable -- its variables now stand for terms only; only an
  axiom's `$T` may depend on a bound variable (doc/kurt-soundness.md §8.31).
- Derivatives and integrals: `load derivative` has continuity `cont x a T`, differentiability
  `diff x a T` and the derivative `deriv x a T` (defined by ε and δ), the rules of
  differentiation with the conditions they need (sum, product, quotient, powers, chain rule, ...),
  Fermat and the mean value theorem; `load integral` has the Riemann integral
  `integral x (a, b) T`, `integrable x (a, b) T`, linearity, splitting, monotonicity and both parts
  of the fundamental theorem of calculus. Examples in proofs/analysis/.
- A schema variable `$T` of an axiom may now also depend on a binder's variable inside the body
  (`deriv $v $a ($S + $T)`), if it is the whole body of a binder over that variable somewhere
  else in the axiom (doc/kurt-doc.md §4).
- Error messages that say what to do: a bound variable named like a constant (rename it), a name
  with `_` (`odd_sum` is read as `odd`, `_`, `sum`), `def f($x, $y)` without `arity f 2`, `def`
  of a symbol declared with `const` before.
- Small laws the course proofs and exercises missed: equality.kurt "not-equal" (`a ≠ b ⇔ ¬(a = b)`,
  to rewrite inside a formula); set.kurt `⊃` ("superset"); field.kurt "zero-plus", "times-one",
  "minus-distributive", "difference-nonzero", "product-one-nonzero". proofs/mafi1/ uses them
  (001 with `⊃` as on the slide; 03, 26, 28 shorter).
- analysis.kurt: the laws of subtraction and halving for ε/2 arguments ("sub-def",
  `a - b = a + (-b)`, and "sub-split", "sub-add", "sub-mul", "sub-zero", "double", "halves",
  "le-mul-nonneg", which follow from it; tests/test_subtraction_laws.py checks their proofs).
- `exercises/`: exercises for students by topic, each loading a scene theory of its topic
  (`theory/`) and stating the questions as `show`s with `todo` proofs;
  `scripts/grade_exercise.py` grades a submission (strict, the statements unchanged).
- A fact derived inside `assume` no longer reports the assumption's fixed `$` variables as new
  constants (`const $x ; added constant`).
- proofs/mafi1/ follows the slides more closely: their names (v1, v2; x1, x2; Kern, Bild), their
  order and their chains (Satz a and b of the groups step by step, with (G4) as an existence
  axiom; (U1) as `U ≠ ∅`; Theorem 5.12, Lemma 5.36, Theorem 5.39 and 6.69 as stated; O(n)
  defined), with intermediate lines removed where Kurt doesn't need them.

## 0.8.2 (2026-10-11)

- The editors are fast again with `load natural` and other large theories: the language server
  (`kurt --lsp`, and the playground) checks a loaded theory once, not on each change of the
  document -- again only when it, or a file it loads, changes (also when it is open in the
  editor). A change of a document with `load natural` took about 4.6 s to check, now 0.06 s.
- The theories embedded in the single-file `kurt.py` (`scripts/build_standalone.py`; the
  playground) are cached too: they were checked again by each file that loads them, and in each
  check -- `load analysis` checked `prop.kurt` five times.
- `RunConfig(progress=...)`: which line of which file is checked, for a progress bar (the
  playground; doc/kurt-doc.md §1). The playground shows it while a check takes a while: a bar
  above the editor, and `Checking natural.kurt · line 120 of 571 · file 2 of 7` (the files
  checked so far: more may follow, as the `load`s are found).

## 0.8.1 (2026-10-10)

- All errors, not only the first: `kurt -a` (`--all-errors`), `RunConfig(all_errors=True)`, and by
  default in the editors (`kurt --lsp`, option `allErrors`) and the playground. After an error in
  the checked file, checking goes on: a formula that can't be derived is admitted, a block that
  doesn't close is closed anyway (its claim admitted), any other line is dropped (with the block
  it opens). Internally only: these lines stay errors, they are no `todo`s, the file gets no
  `.kurtc`, the result is failed; an error in a loaded file, inside `expect`, and a `KernelError`
  still stop. `CheckResult.errors` lists them (`error` is the first), one event each; a
  `Session`'s output shows them at their places, ending with `Proof not checked: N errors.`
- A `.kurtc` is no longer written for a file whose last claim has no proof.
- A proof that doesn't reach its goal is an error at its `show` (where the editors mark it), not at
  the line where it ends: ``the proof of `A and C` (line 4) ends at line 7 without reaching its
  goal -- can not derive `C` ``, also for `qed`.
- The README: the logo (⊢kurt), and the VS Code extension installed with `code --install-extension
  kurt.vsix` (until it is on the Marketplace). The playground's new editor (checked while typing,
  the results in the editor) shows all errors with this release.

## 0.8.0 (2026-10-09)

- The end of a file closes the blocks still open, like a dedent: a proof whose goal is reached
  needs no `qed` there. A proof not finished at the end is a `ProofError` at the line of its
  `show` ("isn't finished at the end of the file"), a claim without proof one at the claim; the
  todos before it still count (an editor marks them). A `Shell` (and the editors' completion)
  continues inside the open blocks. A `qed` that isn't written (a dedent, the end of the file)
  is a derived line after the proof's last line (`qed ; 7a by or-intro(7)`), and the editors show
  it there (`; by 4(3); qed 7a by or-intro(7)`).

- Kurt's output has the number of each source line in front (`   5  B   ; by 3(4)`), and the
  reason goes without it; a derived line keeps its number in the reason (`; 9a by 4`, `; 7-8 by
  impl-intro`). `kurt --no-line-numbers` (and `RunConfig(line_numbers=False)`) prints the old form;
  the interactive shell has no numbers in front (its prompt shows them). In the editors the
  reasons go without their own line's number, and the hover of a line without a certificate says
  what it is (an axiom, a claim, an assumption, ...).
- The editors' hover (`kurt --lsp`) shows the certificate of the line, as `cert` does, with the
  lines it names as links; `CheckResult.certificates` (with `certificates=True`) has them.
- The run state is one object (`RunState`), which a `Session` swaps in as a whole, under a lock:
  sessions can be used from several threads. The command line runs in one `Session` with a
  `RunConfig` from its options. (No change in behaviour; the same output for all files.)
- The error kinds follow one rule: `ScanError` (formerly `SyntaxError`) a symbol can't be scanned;
  `ParseError` the line can't be read; `EvalError` readable but not allowed, now also for wrong
  arguments of a keyword (some were `ParseError`); `TypeError`; `ProofError`. `expect
  "SyntaxError"` becomes `expect "ScanError"` (or `"ParseError"`).
- Fix: a comment at the end of a line inside a statement that continues on the next line
  swallowed the rest of the statement; Kurt's output of a multi-row matrix (with its reason as a
  comment) can be pasted back as source.
- A trusted theory gets a note for a symbol of a theory it doesn't load itself (`∀` via
  `load natural`), and `kurt --deps` lists such symbols for any file; the theories that come with
  Kurt now load everything they use (prop, equality, logic, ... directly).
- The quantifiers `forall`/`exists` are declared in logic.kurt (with `builtin forall universal,
  exists existential`), not in the core: a file with `let` (over terms), `pick` or `∀`/`∃` needs
  `load logic` (numbers.kurt and equality.kurt don't load it).
- `builtin` gives a symbol a meaning built into Kurt: a calculator operation (`builtin + add`,
  formerly `calc + add`; `calc` is now only `calc on`/`calc off`) or a role of the engine
  (`builtin iff equivalence`). Nothing has a meaning by its name alone any more: prop.kurt and
  equality.kurt assign the roles of `iff`, `or`, `not`, `false`, `=`, and only trusted theories
  can (doc/kurt-soundness.md §8.30). New keyword lesson 45-builtin.
- The core is read from `minimal.kurt` when Kurt starts (it was a second copy in `kurt.py`, kept
  in sync by a test); `load minimal` says that it is the core. The comma and space are declared
  quoted there (`infix "," 5 4`).
- Unique existence in logic.kurt: the binder `existsunique`, written `∃! x P(x)` (one symbol,
  `\exists!` in the shell), defined by "existsunique-def" (`∃ x (P(x) ∧ ∀ y (P(y) ⇒ y = x))`),
  also with a condition; the rules "existsunique-intro", "-exists", "-unique" follow from it
  (proofs/natural-deduction/existsunique.kurt). logic.kurt now loads equality.kurt.
- `summary` replaces the inspection keywords `mode`, `level`, `context` and `trail`: the open
  blocks (a `case` block as `case`), the claims still to prove, the latest facts, what could come
  next -- the view of `breakpoint` and `kurt -i`. The keyword lessons 23-26 are one,
  `23-summary.kurt`; the later ones moved up by 3.
- Fix: an `alias` declares its name, so a theory with `alias ∧ and` (prop.kurt) and one with its
  own `∧` (modal.kurt) can't be loaded together -- before, `∧` silently changed its meaning
  (doc/kurt-soundness.md §8.29).
- Fix: `pick FACT` without `with`, with a fact ending in an application with brackets (`pick c > 0
  and P(c)`), read as an unclosed bracket, or crashed with a block after it.
- Fix: `save` keeps what is inside an `expect`, also a statement that only shows something (its
  error may be the expected one) -- the saved file had an `expect` without a body.
- Document the distinct status of conservative `def`initions, `use` axioms, `todo` admissions,
  and derived labelled lines or `show` theorems. Audit the bundled `...-def` rules and replace set
  equality's mutual-subset characterization with a proof from extensionality and subset.
- Explain failed proof steps with a bounded structured `not-derived` result: up to three relevant
  rules, their missing premises, and the premises already matched. Expose it consistently through
  normal errors, `CheckResult.failure`, JSON events, and LSP diagnostic data without treating
  failed one-step search as evidence that a claim is false.
- Add paper-style lambda typing judgments `Γ ⊢ M : A` as an ordinary sorted notation layer over
  the complete de Bruijn rules; retain `has Γ M A` for compatibility. Document the boundary
  between checker sorts and object-level carriers such as `Nat`, retain Boolean-only first-use
  inference, and deprecate the redundant `trail` inspection command in favor of `context` and
  `mode`.
- Complete a follow-up adversarial sort audit, including a forged-certificate regression checked
  by the independent kernel.
- Keep the minimal core free of aliases. `prop.kurt` now owns `⊤`, `⇒`, `∧`, `∨`, and `¬`, while
  `logic.kurt` owns `∀` and `∃`; their canonical words and the quantifier machinery remain in the
  core. This lets a standalone deep theory assign the familiar glyphs to object constructors.
- Replace the incomplete shallow `modal.kurt` with classical normal modal logic T: object
  connectives, K, T, duality, distribution, modus ponens, and necessitation are expressed as
  sorted terms under `⊢`. Convert every modal example.
- Add entirely optional user sorts with `sort nat` and sparse signatures such as
  `nat + 0 1 2`. They reuse `bool`'s positional notation, remain independent of `const`/`var`,
  survive selective theory loading, retain declaration origins, and are available through
  `list` and completion. A declared sort name is exported even before a fact uses it. Sorted
  schema variables remain constrained during search and independent
  kernel verification, including across `load`. `bool` remains the distinguished built-in
  judgment sort. Add packaged `lambda.kurt` with complete de Bruijn typing rules, readable named
  binders, compatible beta reduction, and deterministic call-by-value evaluation, plus lambda and
  modal tutorials. Concrete preservation and local-confluence diamonds document
  what works and why the general metatheorems still require encoded derivations or induction.
- Add `⊢` with the `\vdash` input shortcut and a sorted-term `modal.kurt` theory. Modal
  formulas are terms built with object `→` and `□`; prefix theoremhood and binary sequents share
  `⊢`, and K, object modus ponens, and necessitation are ordinary Kurt schemata. Sequent and
  ordered-resource examples test explicit contexts and the absence of exchange, weakening, and
  contraction. Explicit variables may use Greek names such as `$Γ`, `%φ`, and `$Γ2`, so sequent
  schemas retain conventional notation. These experiments need no generic `rule` keyword:
  ordinary Boolean schemata already express their inference rules.
- Show the effective normalized schema beside a `use` that contains declared named variables,
  for example `; schema: $x $op $y = $y $op $x`. The display uses stable `%` names for Boolean
  variables and `$` names for terms, functions, and operators without exposing internal fresh
  names; structured events include the same schema, while `format source` stays exact.
- Export regressions confirm that named boolean, term, function and operator variables are freshened per formula and
  remain schematic across `load`, including when an importer uses the same names as constants.
- Support `case` over any finite flat disjunction with one exact, kernel-checked `case-elim`
  certificate. It is a bounded derived shortcut justified by a known general binary `or-elim`
  theorem; merely naming an unrelated operator `or` no longer gives it logical semantics. Search
  narrows implications by their common conclusion and checks one per alternative, avoiding a
  generated n-premise rule and its combinatorial matching.
- Show an axiom's optional label on its own `use` output line, as well as on later references to
  that axiom.
- Harden the language server for editor clients: correct UTF-16 positions and file URIs, versioned
  diagnostics, close cleanup, inlay-hint refresh, debounced checks while typing, initialization
  options, and standard shutdown/exit behavior. Open dependencies use their unsaved editor text.
- Keep a document's own directory ahead of extra theory paths without trusting it. Previously the
  LSP represented this search directory as an explicit trusted path, so strict mode could accept
  an unproved `use` from a sibling file.
- Reject declaration combinations that changed normal forms unsoundly: a prefix/infix symbol can
  no longer be `flat`, and binding operators cannot be symmetric, flat, chained,
  calculator-bound, variable, or prefix-overloaded. Complete regressions previously derived
  `false` from satisfiable assumptions.
- Make fixed semantic declarations explicit: `bindop`, `flat`, `sym`, `chain`, and calculator
  bindings imply and report `const`; `chain` also supplies/reports boolean output. Fix bracket
  boolean declarations, validate boolean positions against arity in either declaration order,
  and keep calculator result types consistent with their operations.
- Validate a comma-separated declaration line before changing a persistent shell/LSP session.
  Reject order-dependent arity/fixity/bracket conflicts consistently.
- Add independent truth-table checks for all pure propositional exports and exact sampled checks
  for every `numbers.kurt` axiom.
- Print multirow matrix literals as aligned rows in normal screen output; row vectors, saved Kurt
  source, and s-expression output remain compact and stable.
- Rename the legacy `format original` mode to `format source` and document its contract for
  replaying a stored formula's input spelling.

## 0.7.6 (2026-10-07)

- Add `list`: inspect all retained exports of a loaded theory (`list natural`), narrow them by
  category (`list const natural`, `list theory natural.kurt`), or show loaded files (`list files`).
  Source-filtered output includes original file and line locations; new tutorial and keyword
  lessons document the command.
- Make public publication refuse ignored destination files and exercise the candidate tree in a
  disposable checkout before replacing the real public checkout.
- Add a regression for substitution through a formula nested under another binder.
- Declaration listings (`const`, `var`, `infix`, and the other property keywords without
  arguments) now show the source filename and line alongside the scope level. If loaded files
  have the same basename, the listing uses paths to distinguish them.
- Show every declaration inferred by first formula use in the normal output. This includes a
  constant whose syntax was declared already (`infix ∘ ...`, then `const ∘ ; added constant`)
  and inferred Boolean signatures such as `bool P 0 ; added boolean signature`.
- Fix definition soundness: reject self-reference (including aliases), duplicate definitions and
  forward cycles within a batch, and new function heads with existing semantic declarations.
  Validate the whole batch before adding any facts or declarations, including in strict mode.
  Remove the unsafe “new symbol as argument” form; use `injective(f)` instead of `f is injective`
  when defining a predicate. Complete contradiction regressions cover ordinary and strict checks.
- Fix the language server using a dependency from its launch directory ahead of the document's
  own sibling file; checking and completion now retain the full document source path.

- `kurt -v` (also `-V`, `--version`) shows the version.
- `verbose` is gone (the keyword `verbose on/off` and the option `-v`/`--verbose`): what it showed
  is in the reason of each line and, in full, in `cert N`; the normal form of a term in `parse`
  (and `theory`). The keyword lessons 44-46 are now 43-45.
- Fixes from an external review (dev/astra-suggestions.md, in git history):
  - `def` with the new symbol as an argument of an operator (`$f is injective`) was first
    restricted after an operator bound to the calculator could prove `false`; the 2026-10-07
    follow-up found the form itself unsound and removed it (doc/kurt-soundness.md §§8.22–8.23).
  - `check_text` never trusts a text by its name (`<embedded>/...`, a file in a `-p`
    directory): under `strict`, it may not `use`. The names `<stdin>` and `<shell>` are refused.
  - `kurt --strict foo.kurtc` (and `-p`) checks `foo.kurt` with the options, as `kurt --strict
    foo.kurt` does; `--json` with a `.kurtc` is an error.
  - A session takes a loaded file from its cache only if each `load` of it still finds the same
    file (not a new one earlier in the search path).
  - `check_text` no longer turns `.kurtc` files off for the rest of its session.
  - The Python API refuses `python -O`, as the command line does.
  - Releases: the PyPI and standalone jobs run only after a common job with the tests.
  - The shell with libedit (macOS): Tab works, and the indentation is typed (not filled in).
  - CI: a job on macOS, and one that checks the Lean translation with the Lean of
    `scripts/lean-toolchain` (the tests skip an older Lean, and test a false theorem against a
    true one).
  - Docs: set.kurt's header (mappings are sets of pairs), `.kurtc` from Python, the README's
    lesson counts (checked by a test now).

## 0.7.5 (2026-10-06)

- `kurt --lsp`: a language server for editors (VS Code, Emacs, Neovim): errors and `todo`s as
  diagnostics, the reason of each checked line as an inlay hint and on hover, completion with the
  state at the cursor.
- `kurt.Shell`: the shell as an object, for the playground and editors -- it checks a proof and
  continues where it stopped (its first `breakpoint`, its failing line, or its end); `feed`
  checks more lines there, with `next_steps`, `completions`, `summary`.
- `breakpoint` (instead of `inspect`, which was never implemented): checking stops there and the
  shell continues with the state (at a terminal, or with `kurt -i`); otherwise it shows the state.
  After an error, `kurt -i FILE` continues in the shell at the failing line.
- Tab in the shell: the next step on an empty line, the value after `=` with `calc on`
  (`17*42=` gives `714`), a LaTeX shortcut's symbol, a theory after `load`, keywords, symbols,
  labels. `hint on` prints the next step before each prompt (it did nothing before).
- Vectors and matrices as literals (`load matrix`): `[1, 2, 3]`, `[[1, 2], [3, 4]]`, or one row
  per line; with `calc on`, `+`, `-`, `·`, `transpose`, `det`, `=`, `≠` compute them exactly.
- A symbol bound to the calculator is exported by `load` like an axiom, also without a fact that
  mentions it.
- New theories: `field` (a field `K`, every axiom with its memberships; subtraction and its laws)
  and `vectorspace` (vector spaces over `K`), from proofs/mafi1/, with English labels instead of
  (K1)-(K9), (V1)-(V8).
- One row per line in a matrix only inside a bracket pair bound to `matrix` (`calc [ matrix`).
- proofs/mafi1/ in English: lectures instead of decks, English titles; minimal.kurt's comments up
  to date.

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
