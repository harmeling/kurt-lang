# The logic of Kurt: a specification

This document says what Kurt's logic *is*: which terms there are, which symbols are variables,
when a line follows from the facts before it, what a block proves, what a file exports, and who
may postulate what. It is normative and short; `doc/kurt-ref.md` is the reference of the language
(syntax, keywords, output), `doc/kurt-soundness.md` the audit with its history, and
`doc/kurt-kernel.md` the kernel with examples. Where this document and `src/kurt/kurt.py`
disagree, one of them has a bug; the rules below are the ones the implementation is held to.

In one sentence: Kurt is **first-order natural deduction with schematic rules and declared
normalization**. Its facts are first-order formulas whose free variables are schematic (a fact
stands for all its instances); its rules are such formulas read as `premise ⇒ conclusion`; its
blocks are the introduction and elimination rules of natural deduction; and two terms are the same
when they have the same normal form under the declared associativity, commutativity, and
arithmetic.

## 1. Terms

**1.1 Trees.** A term is a leaf or a node. A leaf is a symbol, a number (an exact integer or
decimal) or a string; a node is an operator applied to one or more terms, `[op, t1, ..., tn]`.
There is no separate syntax for formulas: a formula is a term whose result is a statement (§2).

**1.2 Declared syntax.** How text is read into trees is declared in Kurt source, not fixed in the
implementation: `infix OP lbp rbp`, `prefix OP rbp`, `postfix OP lbp`, `brackets L R`, `arity OP
N` or `arity OP SHAPE`, `binder OP`, `alias NEW OLD`. The core (`minimal.kurt`) declares `( )`
(grouping only), `,` (lists and tuples), space (application), `true`, `implies`, `and` and `sub`.
Application `f a b` is one node `(f a b)`; with `arity f 2` it takes exactly two arguments.
`(a, b)` is a tuple, a term of its own, and `(a, (b, c))`, `((a, b), c)` and `(a, b, c)` are three
different terms. A custom bracket pair is an operator of its own; only `( )` disappears. An alias
is resolved when the text is read: no stored term contains an alias.

**1.3 Normal form.** Every term is stored and compared in its normal form: the arguments of a
`flat` operator are collected into one node (`a + b + c` is `(+ a b c)`), the arguments of a `sym`
operator are sorted into a canonical order (`=` and `iff` keep the order they were written in),
and with `calc on` literal arithmetic of the symbols bound to the calculator is computed. Two terms
are *the same* when their normal forms are equal up to the names of bound variables
(α-equivalence); the arguments of a `sym` operator -- `=` and `iff` included -- are compared as a
multiset. `flat` and `sym` are therefore claims -- associativity and commutativity -- and are
declared before the operator is used in any formula, never for a symbol of a trusted theory (§9),
not for a binder, not for an operator that is also prefix (`flat`), and not for a variable
operator. Declaring either makes the operator a constant.

**1.4 `inline`.** `inline L = R` and `inline L iff R` define a notation: every later occurrence of
the symbol of `L`, applied to arguments for its variables, is *read as* `R`, so the symbol occurs
in no stored term and no stored fact. `inline` has the conditions of `def` (§7.2) and additionally
`R` contains no binder; unlike a `def`, it is not allowed inside a proof block (§6.6).

**1.5 `sub`.** `sub $x $a A` is `A` with `$a` substituted for `$x`, capture-avoiding: a binder in
`A` whose variable occurs free in `$a` is renamed first. `sub` is written only in `use` and `def`
(to state schemas such as "forall-elim" and "equal-elim"), is never nested, and is evaluated when
its variables have values. In the variable slot of a binder, `sub $x $v %C` stands for *any*
condition on the bound variable `$v` (§3.6); such a `%C` is used only as `sub $x ... %C`. Where a
step matches a term against `sub $x $a %A` with `%A` unknown, the hole `$x` ranges over the
subterms -- statements and terms --, at one, several or all of their occurrences. An operator is
no object (§3.1), so the hole is never an operator position: not a function symbol, not an
operator with a statement as its result (`=`, `∧`, a `prop P` of arity 1 or more), not a binder, not a compound operator: in
`c = c` the hole is a `c`, both `c`s or the whole, not the `=` (an operator variable, §3.1,
matches an operator by itself, not as a hole).

## 2. Statements and sorts

**2.1 Statements and terms.** Every expression is a statement (what is proved) or a term (an
object). A symbol has statement places: a list of positions, `0` for its result and `1, 2, ...` for
arguments that are statements (`prop implies 0 1 2`), declared with `prop` or inferred from the
first use of a new symbol, and then final. **Every other place is a term place.** A statement at a
term place, or a term at a statement place, is a type error (a statement is no object, 2026-10-20).
A claim, an assumption, an axiom and a `show` are statements. `%A` is a statement variable by its
name, `$x` a term variable; a statement variable is schematic only -- binders range over terms.
`prop` is no sort: it can't be declared with `sort`, has no subsorts and is below nothing.

**2.2 Sorts.** `sort s` declares a sort; `s OP POS...` declares that a result or argument of `OP`
has it. `any` is a core sort of every file (todo
35), the supersort of every sort: every value fits where `any` is required, and a value of sort
`any` fits no other sorted position. It can't be declared again. Every symbol without a sort is
over all objects, `any`: a variable, a bound variable and a block's constant (one reading, inside a
formula as at its top), and a constant until its first sorted use gives it a sort (§2.4; `any x`
declares one that no use changes). An operator position without a sort takes every value. Every
other sort is a user sort. (There is no sort of the symbols without one, disjoint from the others:
it was unsound with the first sorted use of a constant, decided 2026-10-19.)

**2.3 Subsorts.** An item of a `sort` line is a name or a chain of names, read like `chain`: `sort
set real int` declares the new names and `int ⊂ real ⊂ set`. The subsort relation is the transitive
closure of the declared pairs and has no cycle. A value *fits* a sort `T` iff its sort `S` is `T`
or `S ⊂ T`, or `T` is `any`; a value without a sort fits only where `any` or no sort is required.
A value's sort: a symbol's (declared, inferred,
or of its variable), a number literal's (one sort for all of them), an application's the result
sort of its operator, a `sub`'s that of its body. A position of sort `T` takes only a value that
fits `T` (a type error otherwise); a variable of sort `T` takes only such a value; a binder over
`T` binds a variable of sort `T`, and two binders are the same only over the same sort -- where
a binder over the elements of a set written by its elements (`∀ x ∈ {1, 2}`) counts as one over their
sort; no other set has a sort for its elements. A rule whose bound
variable the author wrote `$$x` (polymorphic: a sort variable of the rule, one sort per use) is used
for a binder of any smaller sort: each `sub` then checks that what it puts in has the variable's
sort. A `$$x` occurs only where it is bound, in `sub`s and as a side of `=` (not in `$$x ∈ $a`: the
elements of the sort matter), it is bound inside the rule (not by an outer `∀`), and it has no sort
of its own. All sorts are inhabited.

**2.3a Overloading (stage 1).** An operator may have several signatures on the same places, when
their sorts are in one chain (`real + 0 1 2`, `complex + 0 1 2`, `real ⊂ complex`); a theory of Kurt
adds one to a symbol of another file, and after the symbol occurs in a fact only a signature above
all it has. The sort of an application is its *least sort*: the smallest signature whose sort every
argument at a sorted place fits (the greatest if none does), from the syntax alone. A place takes
every value that fits the greatest signature; a new constant at a place gets the smallest (so a file
reads as before the overload). A signature is a claim about the model (the carrier of its sort is
closed under the operator), not a fact (doc/kurt-kernel.md §8.5). Decision 19 of dev/todo-sorts.md;
unrelated sorts (ad hoc overloading) are not part of it.

**2.4 Inference: the first sorted use is final.** A symbol without a declared sort gets one when a
line is read: a constant (also one a file loaded without a sort, and the number literals) the sort
of its first sorted use -- the greatest sort that fits all of its places in that line (their meet,
§2.3); where that use also takes smaller sorts and is an element (the left of `∈`, an element of
`{a, b}`), the `default` of the file if it fits; otherwise the position's own sort. Before that, at
places without a sort (`=`, the element of `∈`), it has none: it is any object. The sort it gets is
final (decided 2026-10-19): a later use that doesn't fit -- also at a smaller sort -- is a type error,
naming both places; to use it at a smaller sort, declare that sort before its first use. Not
inferred: a declared sort, the sort of a symbol of a loaded file (it is that file's), a defined symbol
(the sort of its right side), a witness (the sort of the existential's variable), a `$$x`; and a
fact (`x ∈ Nat`) gives none. `=` gives no sort. An operator's place gets a sort only from a
declaration (before its first use) or the `default`. A variable (`$x`, `var`, a bound variable) gets
its sort per formula, from all its places in it (the smallest required; at an element the `default`
decides), without places the `default`, without that `any`; so a formula reads the same wherever it
is read -- an inner `∀ y` and the same `∀ y` as a line of its own (whose variable becomes schematic)
are over the same objects. A constant of a block (`let`, a fixed variable of `assume`) gets its sort
like any constant, and is a variable of that sort in the block's result (§6).

**2.5 `default`.** `default s` (after `sort s`, not `prop`, at the top of a file): from that line
on, every `$` variable, operator position (at the operator's first use, except a statement place; a
binder's variable slot too), bound variable and new constant of the file without a declared or
inferred sort gets `s` -- a new constant at its first appearance, like a declaration. `default any`
is the same as no default (a symbol without a sort is any object anyway: a constant then gets its
sort at its first sorted use). The last `default` counts; it does not cross `load` (§8.2), the sorts
it gave do.

## 3. Symbols: schematic, fixed, bound

Every symbol occurrence in a formula is one of three things: a **schematic variable**, a
**constant**, or a **bound variable**. The kind decides what an instance of the formula is.

**3.1 Schematic variables.** A symbol beginning with `$` (a term) or `%` (a formula) is a variable
by its name; a plain name declared `var x` is a variable too, a term or a formula by its first use.
A fact's free variables are schematic: the fact holds for every instance, where a `$`-variable and
a `var` used as a term take a term, a `%`-variable and a `var` used as a formula take a formula, and
a sorted variable takes a term of its sort. A variable operator (`var ∘` with `infix ∘ 70 70`)
takes an operator. A bare operator (`=`, `∧`, a `prop P` with `arity P 2`) is no formula, although
its signature gives a statement as its result -- that is the result of its application --, so a
`%`-variable never takes one; and an operator is no object (decided 2026-10-20), so a bare
operator with a term as its result is no term either: a `$`-variable doesn't take it, and in a
formula it is a type error, except as the argument of an operator parameter, the place of an
operator variable in the left side of a definition (`(+)` in `group(R, (+), 0, (-))`, by group.kurt's
`def group($G, (∘), $e, (ι)) ⇔ ...`). A function that is a value is a mapping (set.kurt). Each use of a fact renames its variables fresh, so a variable name is never
shared between a fact and a goal. Where a statement is required -- an argument of a connective, a quantifier's body, a
line -- a bare operator (also one with a statement as its result) is a type error (`¬ P` with `arity P 2`, `A ∧ (=)`, `P ⇔ Q`), also
inside an operator that is itself an expression (`(¬ (=)) a b`).

**3.2 Outer universal quantifiers.** When a formula is stored or claimed, its outer `∀`s *without
a condition* are removed and their variables become schematic (a `%`-name stays a statement variable). So `use
∀ x (P x ⇒ Q x)` and `use P $x ⇒ Q $x` are the same fact, and a claim `∀ x P x` is first derived as
`P x'` for a fresh `x'`, then as the whole formula. A `∀` with a condition is not removed; its
meaning is given by rules (§3.6).

**3.3 Constants.** A symbol that is not a variable is a constant: declared `const c`, introduced by
`def`, `let`, `pick`, `brackets`, `binder`, `flat`, `sym`, `chain` or a calculator binding, or used
for the first time in a formula without a declaration (reported as `const c ; added constant`;
with `--strict` an error). On a level, a symbol is constant or variable, never both, and the role
does not change once set; a block's constants are forgotten when the block closes. Numbers are
constants.

**3.4 Fixed variables.** Inside an `assume A` or `case A` block the free variables of `A` are
*fixed*: they are not renamed, not instantiated, and not bound by `let`. In `assume P $x`, `$x` is
one arbitrary object for the whole block (`P $x` follows, `P $y` does not), and closing the block
gives `P $x ⇒ ...`, a schema again. The free variables of a `let` condition other than the `let`
name are fixed in the same way. `let x` (a new name, or a declared `var x`; `let $x` is refused: a `$`-name is always a variable) makes the name a
*constant* of its block; a `$`- or `%`-name made a constant by an enclosing block stays a constant
in nested blocks.

**3.5 Bound variables and scope.** A `binder` has a variable slot (the first argument) and binds
that variable in its *condition* and in its *body*, the last argument. Arguments in between (the
range `(a, b)` of `sum i (a, b) T`, the point `a` of `lim v a T`) are outside the scope: in
`sum x (0, x) x` the `x` of the range is the outer `x`. Bound variables are renamed freely
(α-equivalence); a constant, a schematic variable or an operator is never renamed. A set-builder
`{x ∈ A | P}` is a binder written infix (`|`).

**3.6 Conditions.** The variable slot may hold a condition, `∀ x > 0 P(x)`, `∃ d ∈ A (...)`. The
variable bound by a condition is the first symbol of the condition, as written, that is new or a
variable and not bound by an enclosing binder; it is decided when the line is read and stored with
the condition, so the binder binds the same variable for the rest of the file whatever is a
constant later. A condition without such a symbol is an error. A condition is part of the
formula: `∀ x > 0 P(x)` is not `∀ x (x > 0 ⇒ P(x))`; what a condition means is said by rules
(logic.kurt: "forall-cond-elim", "exists-cond-intro", "forall-cond-def", "exists-cond-def"). A
binder with a condition matches a rule's binder `sub $x $v %C` with `%C` the condition where every
occurrence of the bound variable is the hole `$x`; it never matches a binder without a condition,
and a binder without one never matches `sub $x $v %C`.

**3.7 Instances and bound variables (capture).** A value of a schematic variable must not contain
a variable that is bound at the place where the schematic variable occurs -- except:

- a `%`-variable may (that is what `(∀ $x %A) ⇒ sub $x $a %A` is about); and
- a `$`-variable `$T` of a *postulated* formula (`use`, `def`, `todo`; not a variable of an outer
  `∀` it writes out) may contain the bound variable `$i` if `$T` occurs as the whole body of a
  binder over `$i`, and otherwise only inside binders over `$i` or inside `sub $i ... $T`: such a
  rule uses `$T` only for the bound variable or with something substituted for it, so `$T` stands
  for a term depending on `$i` (`(sum $i ($a, $a) $T) = sub $i $a $T`).

Anywhere else a `$`-variable in the scope of a binder is one fixed term: in `(∀ $x ($x = $T)) ⇒ Q`,
`$T` does not depend on `$x`. A derived fact has no dependent variables, whatever its form: its
variables stand for terms. There is no declaration of dependence and no distinct-variable
condition; the form of the rule decides, and the kernel checks it (§10).

## 4. Facts, levels, and the theory

**4.1 Levels.** A file is checked one level deep (an implicit sandbox); every `proof`, `assume`,
`case`, `let`, `pick`, `sandbox` and `expect` opens a level, closed by a dedent (or `qed`,
`break`, the end of the file). The *theory* at a point is the list of facts of the current level
and of all enclosing levels. A fact of a level and its declarations (`const`, `var`, syntax)
disappear when the level closes; only the formula the closing produces (§6) survives, on the
parent level.

**4.2 Kinds of facts.** How a formula entered the theory is its status; a label never changes it:

| source | status |
|---|---|
| `use F "label"` | axiom: accepted without proof |
| `def c(...) = R`, `def p(...) iff R` | definition: conservative by its form (§7.2) |
| `inline` | notation: in no fact at all |
| `todo F`, a step admitted by `todo` | admitted: the file is "almost checked", never "checked" |
| `assume A`, `case A`, the condition of `let`, the fact of `pick` | hypothesis of its block |
| a line, a `show` whose `proof` closes, the result of a block | derived |
| the rules of `chain`, the rules for `{a, b, c}` | generated axioms (§7.4, §7.5) |

**4.3 Labels and `local`.** `F "label"` names a fact; `F local "label"` names it and keeps it in
its file. A fact is *exported* by `load` iff it has a label and is not `local`.

## 5. The step relation

A line `G` (a claim without keyword, the final goal of a `show`, each conjunct of a conjunction)
is accepted iff one of the following holds for the theory at that point. The order below only
decides which reason Kurt prints. In all cases the free variables of `G` are schematic and
**blocked**: they get no value, so `P $x` claims `P` of everything, and a derived `G` is a fact
for all values of its variables.

**5.1 Truth.** `G` is `true`.

**5.2 Instance.** `G` is an instance of a fact `F`: there are values for the variables of `F`
(§3.1, §3.7) such that `F` with the values is the same term as `G` (§1.3).

**5.3 Rule (modus ponens).** There is a fact `P ⇒ C` -- or a fact `L iff R` with the role
`equivalence`, read as `L ⇒ R` and as `R ⇒ L` -- and values for its variables such that `C` is
`G` and the instance of `P` is *covered*: each conjunct of `P` (flattened) is an instance of a
fact, or a group of conjuncts is an instance of one fact that is a conjunction, or the conjunct
is `∀ y B` and `B` is an instance of a fact with a fresh eigenvariable for `y` -- one that gets no
value, that no `$`-variable of the rule depends on, and that occurs in neither `G` nor a cited
fact. Values are filled in as they are, with the capture rule of §3.7, and `sub` is then
evaluated. One rule, one hop: `C` from `A`, `A ⇒ B`, `B ⇒ C` takes two lines.

**5.4 Conjunction.** `G` is `A ∧ B ∧ ...` and each conjunct is accepted on its own ("and-intro").

**5.5 Case elimination.** `G` is the goal of `case` blocks (§6.1): the theory holds the general
binary rule `(%A ∨ %B) ∧ (%A ⇒ %C) ∧ (%B ⇒ %C) ⇒ %C` ("or-elim", with the role `disjunction`), a
fact `A1 ∨ ... ∨ An`, and for every `Ai` a fact `Ai ⇒ G`.

**5.6 Calculation.** `calc on` is in force (for its level and the levels inside it), and `G` is a
comparison of numbers by a relation bound to the calculator that holds when computed (`3 <= 4`,
`¬(2 = 3)`, `3 ∈ Nat`), or a fact computes to the same normal form as `G` (`x = 5` from
`x = 2 + 3`). The calculator computes exactly (integers, decimals, fractions, the matrices of
matrix.kurt) and computes nothing that has no exact value. A line is stored as written; with `calc
on` it is first searched in computed form against computed facts, then as written.

**5.7 Rewriting.** A special case of 5.3 with a rule of the form `... (sub $x $a %A) ... ⇒ sub $x $b
%A` ("equal-elim", "iff-subst"): `G` differs from a fact at some places. Kurt may add derived
lines of its own before `G` (`17a`, `17b`, ...), each accepted by this relation: the instance
`s = t` of a rule with conditions whose conditions are facts (conditional rewriting), one rewrite
per place for a line that changes up to four places, and `L = L` ("equal-intro") as the fact
before the first line of a chain. A rewrite may replace a group of arguments of a `flat` operator
(any subset if also `sym`, otherwise consecutive ones).

**5.8 Admission.** The line before `G` is a bare `todo`: `G` is admitted (its certificate says
so), and the file is not complete.

**5.9 Restatement.** `G` is the same term as the last fact: it is accepted and not added again.

## 6. Blocks: the rules of natural deduction

A block has a *hypothesis* and *constants* of its own; its *result* is made from its last fact `L`
when it closes. For every block: no individual constant of the block occurs in the result (a
*vocabulary* symbol -- one with an arity, a declared operator, a binder, a `prop` symbol -- may,
except the witness of a `pick`); no symbol that a `def` of the block defined occurs in the result,
whatever it is (§7.2); every binder of the result binds the same variable outside the
block as inside; a constant of the block that has a sort (§2.4: a `let x` that a line made a
number, a fixed `$x` of an `assume`) is a variable of that sort in the result; the block has at
least one fact, and a bare `todo` is not its last line.

**6.1 `assume A` / `case A` (⇒-introduction, ¬-introduction).** `A` is a fact of the block, with its
free variables fixed (§3.4); the conjuncts of a conjunction `A` are facts too if a rule gives them
("and-elim"). The result is `A ⇒ L`. If `L` is the falsum (role `falsum`), additionally `¬A` (role
`negation`). `case` is `assume` whose results are meant for 5.5.

**6.2 `let x1, ..., xn` / `let C` / `let x with C` (∀-introduction).** Each name is new (no constant,
not fixed by an enclosing block) and is a constant of the block; a condition `C` is a fact of the
block, with its other free variables fixed. The result is `∀ xn (... (∀ x1 L))` -- with a
condition, `∀ C L` binding `x` -- in reverse order of the names; a `%`-name gets no quantifier.
Requires the role `universal` (`load logic`).

**6.3 `pick c with F` / `pick F` (∃-elimination).** The theory has a fact `∃ y B` (role
`existential`) with `B[c/y]` the same term as `F`, or `∃ C B` with a condition and `F` the same as
`C[c/y] ∧ B[c/y]` -- or such a fact follows in one step, which Kurt adds as a line of its own. `c`
is new and a constant of the block, `F` a fact of it; `c` has the sort of `y`, and no other (§2.4).
The result is `L`, in which `c` does not occur.

**6.4 `show G`, `proof`, `qed` (a lemma).** `show G` registers a claim on its level; `proof` opens a
block for the latest claim. When the block closes (`qed`, a dedent, the end of the file), `G` is
derived by §5 from the theory at that point, with its free variables blocked; it does not have to
be the block's last line. The proved `G` is a fact of the parent level, with the label of the
`show`. A `qed` that isn't written is a derived line. A claim without a proof at the end of its
file is an error; `break` right after `show` (or after the `break` of its `proof`) withdraws the
claim, which then counts as a `todo`.

**6.5 `sandbox`, `expect "KIND" ["TEXT"]`, `break`.** A `sandbox` is discarded when it closes;
nothing of it survives. An `expect` block must raise an error of the named kind (and message
text) somewhere inside, including while a nested block closes; it is discarded either way, and
closing it without the error is itself an error. `break` closes the innermost block at once and
discards it; it cannot close the file's own level.

**6.6 What a block may not contain.** `use`, `inline`, `chain`, `load` and the declarations of
syntax and sorts (`infix`, `prefix`, `postfix`, `brackets`, `arity`, `binder`, `flat`, `sym`,
`alias`, `sort`, `default`) are not allowed inside `proof`, `assume`, `case`, `let` or `pick`: `use`
and `chain` postulate facts, so the result would look proven although it rests on them; `load` and
the declarations change what the file contains and how it is read, beyond the block; `inline` stays
refused for now (a notation, read away while parsing; dev/todo.md 18). They are allowed at the top
level of a file and anywhere inside a `sandbox` or `expect`, whose content is discarded. A `def` is
allowed in every block (§7.2): it postulates nothing, and it is local to its block.

## 7. Postulates

**7.1 `use F`.** Adds the formula `F` (a statement) as an axiom, schematic in its free variables. Kurt
warns (and does not refuse) when `F` is a bare `%A`, or `%A ⇒ X` / `X iff %A` with `%A` not
occurring in `X`, since these make everything or `X` provable. `use` is the honest spelling of a
recursive, conditional, implicit or characterizing definition.

**7.2 `def L = R` and `def L iff R` (conservative definitions).** Accepted iff:

- `=` has the role `equality` and `iff` the role `equivalence` (equality.kurt, propositional.kurt: they are
  reflexive there, which the argument below needs);
- `L` is one new symbol `c`, or `c` applied -- possibly curried -- to parameters that are distinct
  variables or tuples of distinct variables; `c` is new: used in no fact, not bound to the
  calculator, not `flat`, `sym`, in a `chain`, a binder, or of the core (an `arity`, `prop`,
  `infix` or sort declaration of `c` before the `def` is fine);
- `R` has no free variables other than the parameters, does not contain `c` (aliases are already
  resolved), and is a term for `=`, a formula for `iff`; a constant is no variable, so `R` may
  mention constants -- those of the file, and inside a block those of the block (a `let x`, a `pick`
  witness, a variable fixed by an `assume`, §3.4): fixed objects there, `R` a term about them;
- a comma-separated batch is validated left to right with earlier entries visible, and adds
  nothing unless every entry passes.

**A `def` inside a block** (`proof`, `assume`, `case`, `let`, `pick`; todo 77) is local to it: `c`
is a constant of the block's level and the defining fact a fact of that level; both are gone when
the block closes (its declarations are discarded with the level, §4.1), and the result of the block
(§6) must not mention `c`, whatever `c` is -- an operator or a statement too, unlike the vocabulary
symbols of §6. After the block `c` is an unknown symbol again: a later block may define it anew. At
the top level of a file a `def` is as described above, and exported by `load` if it is labelled
(§8).

Why this is conservative: `c` has no meaning yet, so any model of the theory extends to one in
which `c(x1, ..., xn)` denotes `R` -- the tuples being free (two are equal only if their components
are, set.kurt's "pair-eq") -- and the defining equation holds by reflexivity. Hence the theory with
`def` proves nothing in the old vocabulary that it didn't prove before. Inside a block the same
holds for the theory of the block, whose constants are fixed objects (each model of the block
interprets them), so `R` denotes one value there; nothing derived with `c` leaves the block
except a result without `c`, which is then a consequence of the block's theory alone. That is why
the result must not mention `c`: `let x` / `def k iff P x` as the last line would give
`∀ x (k iff P x)`, in which `k` is no longer a name for one statement (`P c ⇔ P d` would follow);
doc/kurt-soundness.md §8.51. A `def` is a fact like a
`use` and is used by §5.2, §5.3 and §5.7; its status stays `def`. A `def` with a variable only on
the right (`def c = $y`), a recursion (`def liar iff ¬liar`), a non-variable argument
(`def f(a) = a`), or a `def` of an operator with a meaning is refused, since each proves something
new (`1 = 2`, `false`, ...).

**7.3 `todo` and `todo F`.** `todo F` adds `F` as an admitted fact (postulated, §3.7); a bare `todo`
admits the next line (§5.8). Both make the file incomplete.

**7.4 `chain R0 R1 ... Rk` (k ≤ 2).** Each `Ri` is a constant, non-binding infix relation with
a statement as its result (`chain` adds `const` and `prop Ri 0`). The declaration adds, for every ordered pair
(i, j), the axiom `($a Ri $b) ∧ ($b Rj $c) ⇒ ($a Rmax(i,j) $c)` ("chain-trans-i-j"; with
`%`-variables if the relations take formulas): the later relation absorbs the earlier, so `chain =
<` is a different claim than `chain < =`. All chains together form a DAG. Notation that a `chain`
enables: a continuation line `  R t` indented under a line `s R' u` is the line `s R'' t` with `R''`
the relation of the largest index seen so far in the chain, checked by §5 like any line; the same when the line `s` above is a term
and not a statement: `s` and, indented, `R t` are the line `s R t` (a term line that no such line follows is the error "must be a statement" at its line). Independent
of `chain`, `a R b S c` on one line, for relations with a statement as their result, terms as arguments and
the same binding power, is `(a R b) ∧ (b S c)`.

**7.5 Generated rules for sets by their elements.** With set.kurt's roles, each `{a1, ..., an}` in a
line adds to the file's level the axioms "element-i-of-n" (`$yi ∈ {$y1, ..., $yn}`),
"enumeration-n" (`$x ∈ {$y1, ..., $yn} iff $x = $y1 ∨ ... ∨ $x = $yn`), and for a set of constants
of the file "enumeration" of that set. They come from a trusted source, are `local`, and are
checked by the kernel like any rule.

**7.6 `builtin OP role`.** Binds a symbol to a calculator operation (`add`, `lt`, `naturals`,
`element`, `matrixbrackets`, ...) -- an infinite family of axioms (`1 + 1 = 2`, ...) -- or gives it a
role of the engine (`equivalence`, `disjunction`, `negation`, `falsum`, `equality`, `universal`,
`existential`, `setbrackets`, `setbuilder`, `emptyset`): the only way a symbol gets a meaning from
Kurt itself; no symbol has one by its name. A role has one symbol and needs the matching `prop`
signature; roles are assigned only by trusted files (§9).

**7.7 `flat`, `sym`.** Claims of associativity and commutativity, built into the normal form (§1.3).

## 8. Files

**8.1 Each file on its own.** A loaded file is checked in a fresh context: the core plus what it
loads itself -- nothing of the file that loads it. Its exports are then added to the loader.
Hence the order of two `load`s changes nothing either proves, and a proof in a library depends only
on the library's own axioms and loads. A file that is loading already (a cycle) is an error; a file
that finished loading is loaded once.

**8.2 What crosses the boundary (the export bundle).** From a file, `load` brings:

- its exported facts (§4.3), with their internal variable names, sorts and dependent variables;
- the symbols these facts need, plus the symbols bound to the calculator or a role, `inline`,
  `tex` and `lean` symbols, and the symbols the file declares at its top level without `local` -- with
  everything known about each (fixity, arity and shape, `prop`, sorts, `binder`, `flat`, `sym`,
  `alias`, `tex`, `lean`, the file that declared it, the frozen marker), custom brackets, and aliases of
  exported symbols;
- its sorts, its subsorts, the sort of all objects and the sorts of the elements of its sets
  (§2.3), its chains whose relations are all exported, its open `todo`s -- not its `default`
  (§2.5), nor the sort of a `$`-variable's name (its facts carry the sorts of their variables).

Not exported: an unlabelled or `local` fact, a declaration inside a block or with `local`, `var`
(a loaded file's `var n` never makes the loader's `n` a variable: its schemas arrive with internal
variables), the constants Kurt added at first use, `calc on`. A symbol whose `def` is `local` stays
with its definition: an exported fact that needs it is an error, as is an exported fact that needs
a `local` declaration.

**8.3 Validation against the loader.** The bundle is applied only if, for every symbol both sides
know: its declarations do not contradict each other (one side may have more, e.g. a later
calculator binding); it is defined by the same `def` on both sides or by none (a `def` is
conservative only for a new symbol); it is a constant on one side and a variable on the other
nowhere; it is a sort on one side and a term symbol on the other nowhere; it is a statement
(`prop`) on one side and a term on the other nowhere; it is an alias on one side and a symbol of
its own on the other nowhere (unless the same alias); and it is declared (`infix`, `prefix`,
`postfix`, `arity`, `brackets`, `binder`, `flat`, `sym`, `alias`) by one file only. A sort is
declared by one file only, a position of a symbol has one sort on both sides, the subsorts of both
sides together have no cycle, both name the same sort of all objects (or one none), and a set's
elements have one sort. A fact already present (same file, line, label) is added once.

## 9. Trust: who may postulate

**9.1 Trusted sources.** The core `minimal.kurt` (read at the start, never loaded); the theories that
come with Kurt (`src/kurt/theories/`, found by name, never shadowed by a file of the same name
elsewhere); the files in a directory given with `-p DIR` (or the editor's `theoryPaths`); and the
sources Kurt generates (chain transitivity, set enumerations). Everything else is untrusted: the
checked file, a file found next to it or in the working directory, a `load` with a path (`load
./propositional`), text from the shell, an editor's unsaved buffer or Python.

**9.2 Frozen symbols.** The symbols declared by a trusted file are frozen: an untrusted file may
not declare them anew (`infix`, `prop`, ...), make them `flat` or `sym`, or put them into a
`chain` that derives anything new about them (frozen relations may come first in a chain, in an
order their own theory chains them in). An untrusted file may not assign a role of the engine
(§7.6), and `def` defines only with the `=` and `iff` of the trusted theories. An alias in the
loader for a symbol of a loaded file, or the other way round, is refused.

**9.3 `--strict` (grading).** With `--strict`, an untrusted file may not contain `use`, `todo`,
`flat`, `sym`, `builtin` or `save`; its `chain` generates nothing (each rule of §7.4 must be a fact
before the line, or follow in one step); and every symbol must be declared before its first use.
Allowed stay: declarations of syntax and sorts, `def` and `inline` (safe by their form), `calc on`,
proofs, and anything inside a `sandbox` or `expect` (discarded). Trust comes from where a file is
read, never from its name or content; the trusted theories' axioms are trusted by definition.

**9.4 The only source of truth.** Everything Kurt writes (`.kurtc` certificates, `save`, documents)
is either Kurt source that is checked again or hints that the kernel checks again -- never a copy
of facts that is believed.

## 10. The kernel

**10.1 Every step has a certificate.** For each line it accepts, the search produces a certificate
-- the kind of step, the goal, the rule, how it is read (`fact` or `impl`, one direction of an
`iff`), the values of the rule's variables, the facts covering the premise, the fresh names of the
stripped `∀`s, or the block it closes -- and the kernel (`kernel_verify`, `kernel_verify_block`)
checks it without search. A step the kernel rejects does not count: `KernelError` stops the file
and no `expect` catches it.

**10.2 What the kernel checks** for a `rule` step: the rule and each fact are in the theory; only
variables get values, none of the goal's; each value has the kind of its variable (a term or a
formula, §3.1) and fits its sort (§2.3, with the kernel's own reading of the subsorts); a bound
variable of the rule with a variable of another sort as its value is one that occurs only where it
is bound and in `sub`s, and the new sort is smaller; each `sub` puts in a value of its variable's
sort; the
`∀`s are stripped with the recorded fresh names, which are fresh (names only the search makes,
each once, in neither the goal nor a fact, not fixed by a block), get no value, and no
`$`-variable's value depends on them; the values are filled in without renaming, a value
containing a bound variable only where §3.7 allows it, then `sub` is evaluated with the kernel's
own substitution and a computed condition must not contain its own bound variable; the instance of
the conclusion is the goal; the instance of the premise is covered by the facts as in §5.3. For
`top`: the goal is `true`. For `calc`/`calc-fact`: the comparison holds / the fact computes to the
goal. For `case-elim`: the rule is the general binary or-elimination, the first fact a disjunction,
and exactly one implication per alternative, in order, each to the goal. For `todo`: nothing (the
file is incomplete). For a block (`impl-intro`, `not-intro`, `forall-intro`, `exists-elim`): the
block is of the right kind, its cited last line is its last line, the result is the one §6
prescribes, each `let` name and the `pick` witness is new in the block, the picked fact is the
body of a known existential with the witness for its variable, no constant of the block
escapes, no symbol defined by a `def` of the block occurs in the result, a constant of the block with a sort is a variable of that sort (or a smaller one) in the
result, and the witness has at most the sort of the existential's variable.

**10.3 What the kernel trusts.** Its own code; the parser; the normal forms (`flat`, `sym`, the
calculator); the axioms of the theories and the roles they assign; the conservativity check of
`def` (the form of §7.2, checked when the line is read: for the kernel a `def` is a fact of the
theory, like a `use`); and plain helpers. It uses nothing of the search: not its unification, α-equivalence,
substitution or reading of conditions. It re-checks the term/formula distinction of §3.1 with
its own reading of what a formula is (a statement variable or symbol, an operator with a statement as its
result, a `sub` whose body is one): a `$`-variable's value is a term, a `%`-variable's a formula.

**10.4 `.kurtc`.** A stored certificate is a hint: rebuilt against the facts as they are and checked
by the kernel; if that fails, the search runs. A `.kurtc` can make a check faster, never make Kurt
accept more.

## 11. Fixed decisions

The following are part of the logic, not gaps to be closed: one rule per line (no multi-hop
search, no `calc` that solves for an unknown or combines a rewrite with a computation); dependence
of a schematic variable on a bound variable by the form of the rule alone, with no declaration
(§3.7); a recursive definition is a `use`, not a `def` (no termination or constructor checker); a
condition of a binder is a formula part with rules, not an implication built in; no symbol has a
meaning by its name, only by a role a trusted theory assigns; the normal forms are trusted rather
than certified; and the `.kurt` file is the only source of truth.
