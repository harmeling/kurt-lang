# The Kurt Programming Language Reference

**Author:** Stefan Harmeling (implementation); this reference rewritten 2026-09-04 to match the current behaviour of `src/kurt/kurt.py`.

---

This is a reference for the current behaviour of Kurt: what each keyword
does, what the grammar allows, and what is and isn't checked. It describes
things as they are, not as they're planned to become — see `todo.md` and
`todo-claude.md` for planned work, and `dev-notes.md` for the history of
*why* things ended up this way. To actually learn Kurt hands-on, start with
`tutorial/00-true.kurt` and work through the numbered lessons instead; this
document is for looking things up once you already know roughly what you're
looking for.

Every claim below was checked against the interpreter while writing this
document (`kurt <file>.kurt`, or `kurt` interactively), not just read out of
the source.

## 1. Running Kurt

    kurt                        # start the interactive shell (a REPL)
    kurt path/to/proof.kurt     # check a proof file, then exit
    kurt -i path/to/proof.kurt  # check the file, then drop into the shell
    kurt -d path/to/proof.kurt  # also print debug information
    kurt -v path/to/proof.kurt  # also print verbose matching information
    kurt -l path/to/proof.kurt  # emit a LaTeX proof document instead
    kurt -p DIR path/to/proof.kurt   # also search DIR for `load`ed theories
    kurt -r N path/to/proof.kurt     # set the comment/reason column to N (default 42)

If no filename is given, Kurt starts the shell directly. If a filename is
given without `-i`, Kurt checks the whole file, prints `Proof checked` (or,
if any `todo`s are left, `Proof almost checked: N todos.` plus a list of
where they are) and exits with code `1` if checking the file raised an
error (`0` otherwise) — so a script (CI, an autograder) can tell a failed
check from a successful one without scraping stderr text. Leftover `todo`s
still exit `0` (a `todo` is a deliberate, self-reported placeholder, not a
failure), and errors raised only while typing at an interactive shell
session don't affect the exit code either.

**Undocumented-until-now autoload:** before checking the requested file,
`kurt` silently tries to `load` a file literally named `theory.kurt` from
the current directory (or anywhere else on the theory search path, see
§8.2) if one exists, ignoring it quietly if it doesn't. This means a stray
`theory.kurt` sitting in the directory you run `kurt` from becomes part of
*every* proof you check there, without any `load` line asking for it. If
you don't intend this, don't have a file by that name lying around.

## 2. Lexical structure

Kurt reads a proof one *statement* at a time; a statement occupies one or
more physical lines (see §2.1 on indentation/continuation).

- **Comments** start with `;` and run to the end of the line. A comment is
  attached to whatever formula precedes it and can later be shown again
  (e.g. as its label, or via `theory`).
- **Symbols** (identifiers) are `[A-Za-z][A-Za-z0-9]*`, optionally preceded
  by a single `$`, `%`, or `@`. `$` and `%` are meaningful (see §3.2); `@`
  is accepted by the lexer but nothing currently treats it specially.
- **Numbers** are `INT` (`[0-9]+`) or `FLOAT` (`[0-9]+\.[0-9]+`) literals.
- **Strings** are `"..."` (no escaping of embedded quotes); used for labels
  (`use ... "my-label"`) and for some keyword arguments that take an
  operator symbol as text (`infix "+" 20 20`).
- **Operator characters.** Besides letters/digits, `(`, `)`, `{`, `}`, `[`,
  `]`, and `,` are always their own single-character symbols — they never
  glue to each other or to anything else, precisely so a custom `brackets`
  pair keeps working next to unrelated punctuation with no space (e.g. a
  trailing `...}` is two tokens, `...` then `}`, not one token that
  swallows the closing brace). A run of characters from `.:=+-*/#&^'∈!<>|_`
  (note: no brackets in this class) glues together into *one* symbol
  instead (so declaring `!=` gives you a single two-character operator, but
  writing `!!` without spaces is one symbol `!!`, not two `!` tokens). A
  fixed set of additional Unicode symbols is recognised one character at a
  time — exactly the symbols that appear as *values* in Kurt's LaTeX-input
  table (§2.2): the common logic/set-theory symbols (`∀ ∃ ∧ ∨ ⇒ ⇐ ⇔ ¬ ⊤ ⊥ ∈
  ∉ ⊂ ⊆ ⊃ ⊇ ∩ ∪ ∅ ≡ ∘ ↦ → ∞ ≤ ≥ ≠`), modal-logic symbols (`□ ◇`), and the
  Greek alphabet. **Any other non-ASCII character is a lexing error** — you
  cannot declare an operator using an arbitrary Unicode symbol that isn't
  already on this list.
- **`load` is special in the lexer.** A line starting with `load` (case
  insensitive) is scanned specially: everything after it up to a `;` or end
  of line is taken as a comma-separated list of filenames (quoted or bare),
  not parsed as an expression. This is why `load prop, equality` and `load
  "my-theory.kurt"` both work, without `prop`/`equality`/`"my-theory.kurt"`
  needing to be otherwise-valid symbols.

### 2.1 Statements, indentation, and line continuation

A statement can span more than one physical line: if a line ends
mid-expression, Kurt automatically treats the next line as its
continuation — no explicit continuation marker is needed.

In a *file*, indentation is significant. Opening a block (`proof`,
`assume`, `case`, `let`, `pick`, `sandbox`, see §9) requires the next line
to be indented relative to it; dedenting afterwards closes as many nested
blocks as the drop in indentation implies. **A line's indentation is
measured from its very first character, including comment-only lines** — a
comment line indented further than the current block is a `ParseError`
("unexpected increased indentation"), even though it contains no code. In
practice this means: don't visually align a wrapped comment's continuation
under an earlier inline comment by indenting it — keep continuation
comment lines at column 0 (or at the current block's own indentation).
A **blank line**, by contrast, is always safe anywhere, including deep
inside a nested block — it's skipped outright rather than measured, so it
never dedents anything on its own.

### 2.2 LaTeX-style input shortcuts (interactive shell only)

Typing Unicode symbols is inconvenient on most keyboards, so **in the
interactive shell**, before a line is scanned, Kurt rewrites LaTeX-style
commands to their Unicode equivalent: `\forall` → `∀`, `\exists` → `∃`,
`\implies` → `⇒`, `\and`/`\or`/`\not`/`\iff`/`\equiv`/`\top`/`\bottom` →
`∧`/`∨`/`¬`/`⇔`/`≡`/`⊤`/`⊥`, `\in`/`\notin`/`\subset`/`\subseteq`/
`\cup`/`\cap`/`\emptyset`/`\to`/`\mapsto`/`\circ`, `\leq`/`\geq`/`\neq`,
`\box`/`\b`/`\diamond`/`\d` (modal logic), and the full Greek alphabet
(`\alpha`, `\Gamma`, ...). **This replacement only happens for lines typed
at the interactive prompt — it is not applied when reading a `.kurt` file.**
A saved proof file must already contain the real Unicode characters (or use
`alias` to define an ASCII name for them, see §4.7).

## 3. Terms, symbols, and their roles

Every parsed term (`Expr` internally) is either a single symbol/number/
string (a leaf) or an operator applied to one or more sub-terms. There is no
separate "statement" syntax — a term *is* a formula once it's been checked
to be boolean (§5).

### 3.1 Function application is just an infix operator

Space is a built-in infix operator (declared in the hard-coded
`minimal.kurt`, see §8.1), so `f x` means "`f` applied to `x`", and `f x y`
means `f` applied to `x` and then to `y` (i.e. curried, unless `f` has a
declared `arity`, see §4.3, in which case `f x y` is one call with two
arguments). This is also why you can write `not A` even though `not` is
declared as a `prefix` operator elsewhere — a bare `symbol symbol`
juxtaposition is space-application regardless.

### 3.2 Constants vs. variables

Every symbol is exactly one of:

- a **constant** — one fixed, specific object, declared with `const x`, or
  implicitly whenever it's introduced by `let`/`pick`/`def`/`brackets`, or
- a **variable** — may stand for arbitrary objects, declared with `var x`,
  or implicitly the first time an otherwise-undeclared symbol is used in a
  formula (see `bool A, B` in the tutorials: `A`/`B` become variables the
  moment they're first written in an expression, not when `bool` declares
  them — `bool` only records that they're boolean, see §5).

Once a symbol's role is fixed *on a given level* (see §9 on blocks/levels),
it cannot be changed in either direction on that level: declaring `const x`
then `var x` fails, and so does the reverse. A symbol that is a constant
inside a block can still be an ordinary (as-yet-undecided) symbol outside
it, once the block closes and its constants go out of scope.

Symbols starting with `$` or `%` are **always** variables, regardless of
any `const`/`var` declaration — they exist specifically to write *axiom
schemas* in `use` lines (e.g. `use $A implies $A`), where `$x` stands for
an arbitrary non-boolean term and `%A` stands for an arbitrary boolean
formula. You'll see `$`-variables and `%`-variables throughout every
`.kurt` theory file under `src/kurt/theories/`.

### 3.3 What "new" means

Because there's no separate declaration step for most symbols, `const`/
`var`/`bool` mostly exist to be explicit, to catch typos (redeclaring the
same symbol raises an error), and to control what "new" means for keywords
that require a genuinely fresh symbol (`def`, `let`, `pick`, `brackets`).

## 4. Building the grammar

Kurt's grammar is not fixed — the fixity, precedence, and arity of every
operator (including `implies`/`and`/space itself) is declared from Kurt
source, using a small set of keywords, and looked up dynamically by the
parser (a Pratt/TDOP parser). This is what "extensible from Kurt source"
means throughout `CLAUDE.md`.

### 4.1 `infix`, `prefix`, `postfix`

    infix OP lbp rbp     ; e.g. infix "+" 20 20
    prefix OP rbp        ; e.g. prefix "-" 100
    postfix OP lbp       ; e.g. postfix "!" 100

Each accepts a comma-separated list to declare several operators in one
line (e.g. `infix "+" 20 20, "-" 20 20`). Binding powers control precedence
and associativity: for `infix`, `lbp < rbp` makes the operator *right*-
associative (as `implies` is: `infix implies 13 12` — note `13 > 12`, i.e.
*left*-binding-power greater, giving right-associativity: `A implies B
implies C` parses as `A implies (B implies C)`); `lbp == rbp` (as with `+`
above) makes repeated uses ambiguous unless the operator is also declared
`flat` (§4.5). Declaring the same symbol both `infix` and `prefix` is
allowed (useful for something like unary/binary `-`); declaring it as more
than one of `infix`/`prefix`/`postfix`/a bracket otherwise is an error.

Called with no arguments (`infix`, `prefix`, `postfix`), each prints every
currently-declared operator of that kind, across all open levels.

### 4.2 `brackets`

    brackets LEFT RIGHT     ; e.g. brackets "[" "]"

Declares a new matching pair of bracket symbols. **Only Kurt's own `(` `)`
pair (declared exactly this way in `minimal.kurt`) is treated as pure,
disappearing grouping** — `(A)` really is just `A`. Any *other* bracket
pair you declare yourself stays around as a genuine operator: `[A]` parses
to a real term whose operator is an internal name combining `[` and `]`
(rendered as `[]` if you `parse`/`format sexpr` it), not to `A`. Custom brackets
are meant to carry their own meaning (e.g. `|x|` for absolute value, `⟨a,
b⟩` for pairing) via `arity`/`bool`/`use` axioms about the resulting
operator, not as alternative parentheses. `brackets` takes exactly the two
symbols — there is no separate binding-power argument.

### 4.3 `arity`

    arity SYMBOL N     ; e.g. arity f 2

Declares that `SYMBOL` is a plain (non-infix/prefix/postfix) function or
predicate symbol taking exactly `N` arguments by space-application: `f a b`
parses as one call `(f a b)`, not curried. A symbol with no declared arity
defaults to arity 0 and behaves as ordinary curried space-application. You
cannot set an `arity` on a symbol that's already `infix`/`prefix`/`postfix`
or a bracket (their arities — 2, 1, 1 — are implicit and fixed), and you
cannot re-set an arity once declared.

Empty brackets (`()`, `{}`, ...) are allowed and parse to nothing; the only
place this is meaningful is directly after an arity-0 symbol, where `f()`
then parses to *exactly* `f` — the same expression as writing `f` alone,
matching ordinary mathematical usage of `()` for "no arguments." Directly
after a symbol with a declared arity of 1 or more, `f()` is instead a
clear, specific `EvalError` ("empty parentheses `()` cannot supply an
argument for `f`, which needs N argument(s)"), not a confusing parse —
empty parens can never actually supply a real argument.

### 4.4 `bindop`

    bindop SYMBOL     ; e.g. bindop forall

Declares `SYMBOL` a *variable-binding operator*: its first argument is
treated as a bound variable (or, with the sugar below, a boolean condition
whose free variable is the one being bound) for the rest of the
expression. `forall`/`exists` are declared exactly this way — as of this
writing, directly in the hard-coded core (§8.1), not in `logic.kurt`; only
their *axioms* (`forall-elim`, `exists-intro`) still need `load logic`.
Requirements, both enforced: the symbol must already have an `arity` of at
least 2 (the bound variable plus at least one more argument), and it must
not already be declared as any kind of operator or already used in a
formula.

Sugar: the "bound variable" position may instead be a boolean expression
whose leftmost part is the actual variable, e.g. `forall x>0 F(x)` desugars
to `forall x (x > 0 implies F(x))`; the type checker requires that
expression to actually contain a free variable to bind.

### 4.5 `flat` and `sym`

    flat OP     ; e.g. flat "+"
    sym OP      ; e.g. sym "+"

Both require `OP` to already be `infix`. `flat OP` means a run of `OP`
doesn't nest two arguments at a time in the parsed term — `a + b + c`
parses to a single `(+ a b c)` rather than `(+ (+ a b) c)` (compare `parse
a + b + c` before and after declaring `flat`). `sym OP` means `OP`'s
arguments may be reordered when Kurt searches the theory for a match — an
axiom about `a + b` also matches a goal written as `b + a`. An operator
that is *both* `flat` and `sym` (like `and`/`or`) gets its arguments
canonically sorted before matching, which means Kurt effectively does
*multiset* matching on it: `A and B and C` matches a stored `C and A and B`
directly, not just pairwise swaps. Each of `flat`/`sym` can only be
declared once per operator (redeclaring raises an error), and if the
operator already has a partial `bool` signature (§5), that signature must
be consistent with binary use (both argument positions boolean, or
neither; no signature information beyond position 2).

### 4.5a `nonassoc`

    nonassoc OP     ; e.g. nonassoc "<"

Also requires `OP` to already be `infix`. Ordinarily, writing the same
infix operator twice in a row (`a < b < c`) silently parses one way or the
other, decided by the operator's own left/right binding powers — usually
left-associating. `nonassoc OP` makes that a `ParseError` instead:
`a OP b OP c` is rejected as ambiguous, and you must add parentheses
(`(a OP b) OP c` or `a OP (b OP c)`) to say which one you mean. Mutually
exclusive with `flat` (declaring either one after the other is an error) —
a `flat` operator is inherently associative by construction, the opposite
of what `nonassoc` asserts. Can only be declared once per operator.

### 4.6 `chain`

    chain OP1 OP2 ...     ; e.g. chain = <=  or  chain iff implies

Declares that the listed infix operators may be written one after another
across indented continuation lines, mimicking how mathematicians chain
(in)equalities: after a chain is declared, writing

    x = y
      < z

is sugar for two separate checked lines, `x = y` and `x < z` (the second
line's left-hand side is filled in from the previous line's right-hand
side, and the operator used is the *strongest* one seen so far in the
chain, by index in the declared list — this is why `chain = <` lets `= ,
<`-chains resolve to `<` once a `<` has appeared).

Declaring a chain also generates real, directly usable transitivity
axioms — one for every ordered pair of the chain's operators, using the
same "pick the operator with the larger index" rule as the parsing sugar
above. For `chain = <= <`, that includes the familiar `$a < $b and
$b < $c implies $a < $c` ("lt-trans"), but also every *mixed* pair like
`$a <= $b and $b < $c implies $a < $c`. So given `x = y` and `y < z` as
two separately-proven facts (not written as one continuation-line chain),
`x < z` really is now a single derivation step, citing the
auto-generated fact — you don't need to hand-write these per theory
(`arith.kurt` used to; it no longer does). This only combines *two*
facts in one hop, the same as every other inference rule — three or more
links in a chain of relations still need an explicit intermediate step,
same as any other multi-hop reasoning (§6.1's single-hop limitation still
applies beyond one combination).

Relations can also be chained on a single line: `a = b <= c < d` means `a =
b and b <= c and c < d`, reusing each middle term. This applies to any infix
operator with a boolean result and no boolean arguments (`bool OP 0`, e.g.
`=`, `≠`, `<`, `<=`, `in`), whether or not it is declared in a `chain` —
not to connectives like `and`, `iff`, `implies`. Parentheses switch it off:
`(a = b) = c` is still an equation between `a = b` and `c`. Since the
auto-generated transitivity axioms take a conjunction as premise, a single
chained line like `a = b <= c` directly gives `a <= c` in one more step
(`proofs/arithmetic/chains.kurt`). A same-line chain can't (yet) be
continued on indented lines below it.

Continuation lines must be indented relative to the line that starts the
chain; writing the continuation at the same indentation is a `ParseError`,
not a chain. All declared chains together must form a DAG (no operator
ordering may create a cycle across different `chain` declarations) — this
is checked when the chain is declared.

### 4.7 `alias` and `latex`

    alias NEW OLD     ; e.g. alias "⇒" implies
    latex SYM REPL     ; e.g. latex "xor" "\oplus"

`alias` gives an existing symbol an additional name, resolved *in the
scanner* (i.e. before parsing, with no inference step) — `implies` and `⇒`
are completely interchangeable everywhere, including inside axioms already
stored in the theory. This is different from `def` (§6.2), which
introduces a genuinely new constant that needs an inference step
(`equal-elim`/`iff-elim`) to unfold.

`latex` records how a symbol should render in a generated LaTeX proof
document (`kurt -l`); it has no effect on parsing or proving. `format latex`
also switches the *session's* print format to LaTeX from inside a `.kurt`
file (§10) — note this is a separate thing from the `-l` command-line flag,
which generates a whole LaTeX proof document rather than just changing how
formulas print in the shell.

### 4.8 Inspecting the grammar

`syntax` (with no argument) prints every declared piece of syntax at every
open level; `syntax SYMBOL` prints just what's known about one symbol.
`parse EXPR` parses `EXPR` without checking it and prints both its
s-expression form and the same per-symbol syntax info as `syntax`.
`tokenize EXPR` shows the raw token stream before parsing. Each of
`infix`/`prefix`/`postfix`/`brackets`/`arity`/`bindop`/`flat`/`sym`/
`nonassoc`/`chain`/`bool`/`var`/`const`/`alias`/`latex`, called with no
arguments, also prints its own currently-declared table.

## 5. Boolean typing

    bool SYMBOL              ; SYMBOL's own value is boolean
    bool SYMBOL POS...       ; also: argument(s) at these 1-based POSitions must be boolean

Kurt does a light, non-recursive-by-default type check: `bool_expr` asks
"is this one term boolean at the top?", and `type_check_expression` walks
down recursively, checking each operator's declared *bool signature* — a
list of integers where `0` means "this symbol's own result is boolean" and
`1`, `2`, `3`, ... mean "argument N must itself be boolean". So `bool
implies 0 1 2` (from `minimal.kurt`) says: `implies` produces a boolean,
*and* both of its arguments must themselves be boolean formulas — which is
why `A implies B` type-checks only once `A` and `B` are themselves boolean
(directly, or transitively). A symbol with no declared `bool` signature at
all is *not* required to be boolean anywhere, and an as-yet-undeclared,
never-used symbol is optimistically treated as "probably about to be used
as boolean" the first time it's mentioned in a position that needs one
(e.g. plain `bool A, B` followed by using `A`/`B` in a formula).

A boolean *variable* (as opposed to a boolean-valued *operator*) is written
with a leading `%` inside a `use` schema (`%A`, `%B`, ...) — see §3.2.

Only `use`/`show`/bare top-level claims are required to be boolean overall
(the exact error is "must evaluate to boolean"); nested sub-terms are
boolean only where the enclosing operator's signature says they must be.

## 6. The theory: making and using claims

The **theory** is the accumulated list of `Formula`s (axioms, definitions,
and proven facts) currently in scope. Kurt is a single-pass checker: each
top-level statement is scanned, parsed, type-checked, and evaluated in
order, and generally either succeeds (and is appended to the theory) or
raises an exception (and, in a file, stops checking).

### 6.1 Bare claims

A line that's just an expression (no leading keyword) is a **claim**: Kurt
tries to derive it from the current theory and, if it succeeds, adds it to
the theory. If it's a conjunction, each conjunct may be derived separately
and then combined via "and-intro" (this, and "impl-elim"/modus-ponens
against every formula currently in scope, and "top-intro" for the literal
symbol `true`, are the only rules hard-coded directly in Python — see
§8.1). Derivation is a *single* hop: given `A`, `A implies B`, and `B
implies C` all separately in the theory, deriving `C` in one step is *not*
automatic — you must first derive `B` as its own line. See
`todo-claude.md` for the design questions around making this multi-hop.

A claim that's structurally identical to the last thing already in the
theory is silently treated as a no-op restatement rather than logged again.

Labelling (§6.2) isn't specific to `use`/`def` — it's the same mechanism
for *every* statement, keyworded or not, since they're all parsed through
the same `check_expr_label`. A bare claim can be labelled, and marked
`local`, exactly like an axiom can:

    use P implies Q
    use P
    Q  "derived-q"        ; a label on a bare, derived claim works too

and this is what actually decides whether `Q` is exported when this file
is `load`ed elsewhere (§8.2) — not whether it came from `use` or was
derived as a bare claim.

### 6.2 `use` and `def`

    use EXPR              ; use EXPR "label"
    use EXPR local "label"
    def SYMBOL = EXPR
    def SYMBOL iff EXPR

`use` adds `EXPR` to the theory as an **axiom** — accepted without proof.
An optional trailing string labels it (shown in later log lines and error
messages instead of a bare line number). The label also controls whether
`EXPR` is *exported* when this file is `load`ed elsewhere — see §8.2 —
unless it's marked `local`, in which case the label is still used for
display but the fact stays private to this file. `show`/`proof`/`qed` (§7)
and `def` follow the exact same rule: `def`'s label controls whether the
symbol it introduces is (indirectly) exportable, and a proved theorem's
`show` label carries forward to the final proved formula.

Since a bare `%`/`$` schema variable in a `use`/`def` axiom means "for any
value of this symbol", it's easy to accidentally write an axiom that's far
stronger than intended — e.g. `use %A` literally asserts "every proposition
is true", and `use %A implies P` (with `%A` not reappearing anywhere in `P`)
makes `P` derivable completely unconditionally, since `%A` freely unifies
with anything. Kurt prints a `Warning:` to stderr (not an error — such an
axiom is occasionally written on purpose) when a `use`/`def` matches one of
these obvious shapes; see `doc/kurt-soundness.md` §6 for the full
explanation and its limits (it only catches a few syntactic patterns, not
every equivalent phrasing).

`def` is `use` specialised to introducing exactly one **brand-new**
constant via an equation (`=`) or equivalence (`iff`) — the only two
top-level operators `def` accepts. Exactly one new symbol must appear on
the **left-hand side** (e.g. `def x = 18`, or `def Pow($a) = { $b | $b ⊂
$a }` — the new symbol doesn't have to be the very first token, just
somewhere on the left); the right-hand side must contain no new symbols at
all (only already-declared constants/variables, or `$`/`%` schema
variables). `def` needs `=`/`iff` to already
exist as operators, which means (unlike `use`) it can't be demonstrated
against the bare `minimal.kurt` theory — you need `load equality` (for
`=`) or `load prop` (for `iff`) first. Both `use` and `def`, called with no
arguments, print everything `use`d/`def`ined so far.

### 6.3 `todo`

    todo          ; admit whatever the current goal is
    todo EXPR      ; admit EXPR specifically, and add it to the theory

A joker: lets a proof continue (and the file still finish, with `Proof
almost checked: N todos.` instead of `Proof checked`, listing every
`todo`'s file and line) even though a step hasn't actually been justified.
Meant for iteratively developing a proof, or handing out a skeleton with
gaps left as exercises.

### 6.4 `theory`

    theory              ; print every formula, at every open level
    theory OP            ; print only formulas whose top-level operator is OP

Read-only introspection; changes nothing.

## 7. Goal-directed proof: `show` / `proof` / `qed`

    show EXPR              ; show EXPR "label"
    proof
        ...
    qed

`show` states a goal without proving it yet; it must always be followed
(immediately, or after other statements) by a matching `proof` — `proof`
refuses to open if there's no pending `show` on the current level. Inside
`proof`, you may write any number of intermediate steps, checked exactly
like top-level statements. Closing the block **re-derives the shown goal
from scratch**, using everything true at that point (not by comparing to
the block's literal last line) — so a block whose last explicit line looks
unrelated to the goal can still close successfully, as long as the goal
happens to already be derivable by then. If the goal can't be (re-)derived,
the block does not close (a `ProofError`, either from `qed` itself or from
the dedent that was trying to close it).

`qed` is optional: dedenting alone already closes a `proof` block the same
way (§9 covers dedent-based closing in general). Writing `qed` additionally
checks that you really are closing a `proof` and not some other kind of
block, and documents where the proof ends; either way, `qed` must line up
with the indentation of the `proof`/`show` it's closing — dedenting is how
Kurt knows how many nested blocks to close, and a single `qed` can close
several at once this way. This is identical in a file and in the
interactive shell — see §9's introduction.

`thus` is an alternative to `qed` (and to plain dedenting) for closing a
`proof` block: instead of re-deriving the goal from scratch, it only checks
that the block's *last line is already, literally, the goal* (up to
alpha-equivalence of bound variables — the same notion of "the same
formula" used elsewhere, e.g. by `use`/`show` restatement checks). No
search happens at all, so `thus` is cheap and its outcome is easy to
predict just by reading the last line, but it also means `thus` rejects a
proof whose last line is one step short of the goal even when `qed` would
happily take that step — write out that last step explicitly, or use `qed`
instead. Like `qed`, `thus` must line up with the `proof`/`show` it closes
and can only close a `proof` block (not `assume`/`case`/`let`/`pick` —
those close with `qed`/dedent only). Prefer `thus` for long equational or
`iff`-chain proofs where every line already restates the goal-so-far.

## 8. Building the theory: hard-coded core vs. loaded theories

### 8.1 What's hard-coded (needs no `load`)

A pristine session starts with `minimal.kurt`'s worth of syntax (space,
comma, `(` `)`, `implies`, `and`, the constant `true`, the substitution
operator `sub`, and — see below — `forall`/`exists`) already declared,
plus these rules implemented directly in Python (not as `use` axioms you
could remove):

- **"top-intro"** — the bare symbol `true` is always provable.
- **"impl-elim"** (modus ponens) — given `A` and `A implies B` anywhere in
  the theory, `B` is derivable.
- **"and-intro"** — given `A` and `B` separately provable, `A and B` is
  derivable (and, symmetrically, a claimed conjunction is split into its
  conjuncts and each is derived separately).
- **"not-intro"**, automatically, as a side effect of closing an `assume`
  block (see §9.1) whose last derived line is literally `false` — this one
  isn't reachable as a standalone rule outside of that block-closing
  moment.
- **forall-elim, effectively for free** — every formula ever added to the
  theory has any *outer* `forall` automatically stripped and its bound
  variable replaced by a fresh, freely-unifiable internal variable (as if
  it had been written as a `$`-schema to begin with) — so `use forall x A
  x` already lets `A a` derive for a specific `a`, with no `load logic` and
  no explicit `forall-elim` step needed. `logic.kurt`'s `forall-elim` axiom
  still exists for the same reason a hard-coded rule sometimes also has a
  `use` equivalent lying around: explicit intermediate steps, and cases
  this automatic stripping doesn't reach (a `forall` that isn't the
  outermost operator of a stored formula).

`forall`/`exists`'s *syntax* specifically (their `arity`/`bindop`/`bool`
declarations and `∀`/`∃` aliases — not their axioms, which are still only
available via `load logic`) is hard-coded for a reason beyond consistency
with `and`/`implies`: the forall-elim behavior just described, and the
theory-search machinery behind it, are *unconditional* — they run on every
formula regardless of whether any theory has declared `forall` a `bindop`.
Before this was hard-coded, using the bare word `forall` for anything, with
no `load logic`, crashed outright the first time that machinery saw it
(the auto-stripping code assumed the shape only a real `bindop` parse
produces) rather than just failing to do anything useful.

Notably, **"and-elim"** (splitting a proven `A and B` back into `A`) is
*not* hard-coded — you either state the specific instance yourself as a
`use` axiom, or `load prop` for a general one. A general "restatement"
schema (`$A implies $A`) and a general "impl-intro" schema (`($A implies
$B) implies ($A implies $B)`) are *also* not hard-coded, despite once
being drafted as if they were: a bare `A implies A` with nothing else
known does not derive from nothing. Prove a specific instance instead
(`show`/`proof`/`assume`/`qed`), or note that plain "restating" an
already-proven fact is covered anyway by "impl-elim"'s own premise-less-
implication case.

`minimal.kurt` itself is never meant to be `load`ed (its first line is
`false`, so loading it always fails) — it exists purely as a
human-readable description of the pristine starting point.

### 8.2 `load` and the theory library

    load NAME               ; load "path/to/name.kurt"
    load NAME1, NAME2, ...

`load` searches, in order: the loading file's own directory (or the
current directory, from the CLI/shell), then any `-p`/`--path` directory
given on the command line, then Kurt's own packaged theories
(`src/kurt/theories/`). The `.kurt` extension is added automatically if
missing. A file that has *already finished* loading is not loaded again
(tracked via `get_load_level`, per level, inherited from parent levels) —
so `load prop` twice in a row, or from two different files that both
depend on it, is a harmless no-op rather than a duplicate-axiom error. A
file that is still *in the middle* of loading (a genuine cycle: `a.kurt`
has `load "b.kurt"`, and `b.kurt` has `load "a.kurt"`) is tracked
separately and raises a clean `EvalError: circular \`load\`: ...` instead
of recursing forever. Loading happens inside its own temporary
level, so a file that leaves a block unexpectedly open (an unmatched
`assume`/`let`/`pick`/`proof`/`sandbox`) fails the whole `load` rather than
silently leaking a half-open block into your file.

The packaged theories (`src/kurt/theories/`), and roughly what each adds,
declaring their own prerequisites via their own `load` lines:

| theory | adds | depends on |
|---|---|---|
| `prop.kurt` | `or`, `not`, `iff`, `invimplies`, `false`; and-elim, or-intro/elim, iff-intro/elim, not-intro/elim, bottom-intro/elim | (none — builds on the hard-coded core) |
| `equality.kurt` | `=`, `≠`; equal-intro/elim | `prop` |
| `logic.kurt` | forall-elim, exists-intro (`forall`/`∀`/`exists`/`∃` themselves are hard-coded, §8.1) | `prop` |
| `set.kurt` | `in`/`∈`, `⊂`, `∪`, `∩`, set-builder `{ ... \| ... }`, `∅`, `Pow`, mappings (`→`, function-space membership, function-extensionality) | `equality`, `logic` |
| `arith.kurt` | arithmetic | `equality` |
| `natural.kurt` | natural numbers, induction | `set`, `arith` |
| `modal.kurt` | modal logic (`□`, `◇`) | `prop` |
| `latex.kurt` | LaTeX rendering setup for `kurt -l` | none declared |
| `lambda-calculus.kurt` | `λ`/lambda abstraction and beta-reduction (a *predicate* lambda calculus — see the file's own header for why: single-argument, boolean-bodied only, no currying, no eta) | `equality` |

`load` with no arguments lists every file loaded so far, level by level.

#### What gets exported

Not everything a loaded file declares becomes visible to whoever loads it.
A `use`/`def` axiom or a proved (`show`/`proof`/`qed`) theorem is
**exported** exactly when it carries a label and that label isn't marked
`local` (§6.2) — an unlabelled fact, or one labelled `EXPR local "..."`,
stays entirely inside the file that wrote it. Symbols work the same way,
but with no separate marking of their own: a symbol is exported exactly
when some exported fact actually mentions it (its arity, fixity, boolean
signature, and so on all travel along with it, so the fact can still be
parsed and type-checked downstream); a symbol that only ever appears in
local facts is invisible from outside too, freeing up its name for
something else entirely unrelated in whatever file loads this one. An
alias (`alias`) travels automatically with whatever symbol it names, since
an alias never itself appears written out in a formula — axioms are always
written with the canonical name.

This makes `def`'s two halves — the new symbol, and the fact defining what
it means — travel together when exported. If a `def` is marked `local` but
some *other*, exported fact in the same file still needs that symbol, the
file fails to load with a clear error naming the symbol, rather than
silently promoting the `local` marking away or silently leaving the symbol
meaningless downstream.

Variables (`var`, and free variables' scoping generally) are always
file-local regardless of labelling — this was already true before the
label/`local` mechanism existed.

Example:

    ; helper.kurt
    load prop
    bool P, Q
    use P            "exported"      ; travels to whoever loads helper.kurt
    use Q            local "hidden"  ; stays inside helper.kurt
    def R iff P      "also exported" ; R travels too, since it's labelled

    ; main.kurt
    load helper
    P                 ; fine -- P was exported
    R                 ; fine -- R (and its definition) was exported
    Q                 ; ProofError: can not derive `Q` -- never exported, so as far as
                      ; main.kurt is concerned `Q` is just a fresh symbol with no axiom
                      ; behind it (§5), not literally an "unknown symbol" error

#### `save`: the reverse of `load`

    save "path/to/file.kurt"

Writes the current, fully-built-up state — every syntax declaration and
theory fact from every level below and including the current one (but
*not* level 0, the pristine hard-coded core described in §8.1, since
that's already present in any fresh session) — out to `path` as
self-contained `.kurt` source, in a form that reconstructs the same state
via a plain `load` (path is resolved relative to the current working
directory, same as any other file write, not relative to the file being
run). `save` is a flat snapshot, not a recording: every fact is re-emitted
as a `use`/`def`/`todo` statement regardless of how it was originally
obtained — including one proved via `show`/`proof`/`qed`/`thus` — so
reloading it never re-runs any proof search. Every fact is given a label,
synthesizing one (`"save-1"`, `"save-2"`, ...) for any fact that didn't
already have one, so nothing is silently dropped by `load`'s selective
export (immediately above) if the saved file is later `load`ed from
somewhere else rather than run directly. Only the theory and syntax are
saved — a pending `show` goal or an open proof/`assume`/`let`/`pick` block
is not; call `save` once everything is settled (`root`/`sandbox` level),
not mid-proof. `save` also deliberately does not try to detect "this came
from `load prop`" and write `load prop` instead of `prop`'s own facts —
that would need to reliably tell a loaded theory's facts apart from ones
added locally, for a saving that's only sometimes smaller.

## 9. Blocks and natural deduction

Every open `proof`/`assume`/`case`/`let`/`pick`/`sandbox`/`expect` pushes a
new **level** onto the knowledge base (`level` prints how deep you are;
`mode` prints the current level's kind — `root`/`proof`/`assume`/`let`/
`pick`/`sandbox`/`expect`; `trail` prints the whole chain of modes on one
line; `context` prints the same thing with more detail per level). A
block's own `const`/`var` declarations and any axioms `use`d inside it
disappear again once the block closes; only the formula the block's
closing produces survives, on the *parent* level.

**Indentation drives block closing, identically whether you're reading a
file or typing/pasting into the interactive shell.** Dedenting — writing
(or, in the shell, typing) a line less indented than the block's content —
closes as many levels as the drop in indentation implies, applying
whatever each level's closing rule is (`impl-intro`, `forall-intro`, ...,
below). There is no separate "shell mode" for this: the interactive shell
reads real leading whitespace exactly like a file does, so pasting file
content into `kurt -i` behaves the same as running it as a file. Four
keywords remain as *optional*, position-independent alternatives to
dedenting, and work identically in files and the shell: `qed` (§7 — still
needs a real dedent, but also checks you're closing a `proof`), `thus`
(§7 — also still needs a real dedent and only closes a `proof`, but checks
the goal by literal match instead of re-deriving it), `break` (§9.5 —
needs no dedent at all, and is the only way to close a `sandbox` other
than dedenting past it), and `commit` (§9.5 — `break`'s opposite: also
needs no dedent, but keeps a `sandbox`'s content instead of discarding it).

**Running a file itself already starts one level deep, inside an implicit
`sandbox`** (the same mechanism `load` uses, see §8.2) — so `mode`/`level`
at the very top of a file report `sandbox`/`1`, not `root`/`0`.

### 9.1 `assume` and `case`

    assume EXPR
        ...
    (closes by dedenting, or `qed`/`break`)

Opens a block that adds `EXPR` as a local axiom. Closing it derives
"impl-intro": whatever you proved last inside the block becomes `EXPR
implies <that>`, on the parent level. If the last thing derived inside the
block was literally `false`, closing *additionally* derives `not EXPR` via
"not-intro" (both formulas are added). `case` is handled identically to
`assume` (there is currently no extra checking specific to `case`, see
`todo-claude.md`) — it's meant to be used as a sequence of `case`s covering
a disjunction, each producing its own `EXPR implies <goal>`; actually
concluding the goal from all the cases (or-elim) then needs **two** things
already in scope, not just the sequence of `case` blocks itself: the `or`
theory's `or-elim` axiom (from `load prop`), *and* the disjunction fact
itself (`%A or %B`, covering exactly the case expressions used) as its own
derivable/`use`d line — Kurt never checks that your `case`s are actually
exhaustive, it just needs the real disjunction to exist. Forgetting either
piece (the disjunction fact, or the final explicit claim restating the
goal after the cases close, needed to trigger the match) is the most
common way a `case` proof silently doesn't finish — it fails with an
ordinary "can not derive" on that final line, not a `case`-specific error.

### 9.2 `let`

    let SYMBOL             ; or a comma-separated list: let x, y, z
    let SYMBOL CONDITION    ; e.g. let x>0
        ...

Introduces one or more brand-new constants (each must not already be a
declared constant). A condition (`let x>0`) also `use`s the condition as a
local axiom, in one step. Closing the block derives "forall-intro": the
last thing proven inside becomes universally quantified over each new
constant, in reverse declaration order, skipping any that turn out to be
boolean variables. (`let`'s error messages, as of this writing, still say
"`fix`" — an old name for this keyword — see `todo-claude.md`.)

### 9.3 `pick`

    pick SYMBOL with FACT
        ...

Requires some already-known formula `exists $x P` in the theory such that
substituting the new `SYMBOL` for `$x` in `P` gives exactly `FACT`; if
found, opens a block with `SYMBOL` as a new constant and `FACT` as a local
axiom. Closing the block derives "exists-elim": the last formula proven
inside must not mention `SYMBOL` (checked, and also not mention any other
constant introduced on the block's own level) — with that check passed, it
becomes the block's result on the parent level, without any reference to
the witness.

`SYMBOL` must be a bare new-or-existing name, unlike `let`'s otherwise
similar `let SYMBOL` / `let SYMBOL>0` (§9.2) — a `pick`ed witness can never
carry an extra condition of its own the way a `let`-bound one can: `let`'s
condition becomes an assumption that gets quantified away when the block
closes, but a `pick`ed witness is existential, so an unearned extra
condition on it would just be an unproven fact about a specific value, not
a sound derivation. `pick x>0 with FACT` is therefore rejected outright
(`EvalError`) rather than silently accepted or silently ignored; the
witness's only property comes from `FACT` itself.

### 9.4 `sandbox`

    sandbox
        ...
    (closes by dedenting, discarding everything inside -- or by `break`, immediately --
     or, to keep it instead of discarding it, by `commit`)

A scratch block: everything inside is discarded by default, never merged
into the surrounding theory, whether it closes by dedenting (§9's
introduction) or by `break` (§9.5) right away. `commit` (§9.5) is the
exception: it closes a `sandbox` immediately, like `break`, but keeps its
content instead. A file with an unclosed `sandbox` at end-of-file still
fails with `EvalError: ... not all blocks closed`, same as any other
unclosed block.

### 9.5 `break` and `commit`

    break     ; discard the current block immediately, without proving anything
    commit    ; close a `sandbox` immediately, keeping its content instead of discarding it

`break` closes the current block right away, discarding it — no
`impl-intro`, `forall-intro`, etc., nothing is added anywhere — without
needing to dedent past it first. Works identically in a file or the
interactive shell, and on any open block. Breaking out of a `proof` also
gives up the pending `show` it was trying to prove, not just the `proof`
block itself, so nothing is left dangling on the parent level.

`commit` is `break`'s opposite: it only ever closes a `sandbox` (every
other block already has its own way to keep what happened inside — dedent,
or `qed`/`thus` — so `commit` on one of those is rejected rather than
silently doing something else), and instead of discarding its content, it
keeps it — via the same selective export a `load` uses (§8.2's "What gets
exported"): only a labelled, non-`local` fact (and the symbols it needs)
travels to the parent level, exactly as if the sandbox's content had been
a separate file the parent `load`ed. An unlabelled fact tried out inside
the sandbox stays scratch even after `commit`, same as it would in a
loaded file. Neither `break` nor `commit` can close the file's own
implicit top-level scope (§8.2, §9's introduction) — there is no real,
user-written block there to close, so both raise a clean error rather than
doing anything to it.

### 9.6 `expect`

    expect "KIND"
        ...

Opens a block whose content is *expected to raise* an error of the given
`KIND` — one of `ProofError`, `ParseError`, `EvalError`, `SyntaxError`,
`TypeError` (every `KurtException` carries a `.kind`, derived from the
conventional string prefix at the start of its message — see
`KurtException.KNOWN_KINDS` in `kurt.py`). If something inside the block
raises exactly that kind, the whole block (including anything it did) is
discarded and checking simply continues with the next statement, the same
way `break` discards a `sandbox`. If the block closes normally with nothing
having raised, *that itself* is now the failure (`ExpectationError: this
\`expect "KIND"\` block finished without raising a \`KIND\``); if something
raises but of the *wrong* kind, that's also a failure, reported with both
kinds shown.

This exists so a proof file (or a lesson, see `tutorial/15-expect.kurt`) can
demonstrate a mistake and have Kurt itself confirm it still fails the
expected way, rather than relying on a comment nobody re-checks, or on a
separate test harness matching exact (and therefore fragile — see
`todo-claude.md`) error text.

**Current limitation:** `expect` can only observe a failure raised by an
*ordinary statement* directly inside its own body — never a failure that
happens while *closing* a block (its own body's nested block, or even the
preceding sibling block that this `expect` line's own dedent happens to
close). In both cases, at the moment the exception is caught, the current
mode is that other block's own mode (`proof`, `let`, `pick`, ...), not
`expect` — so `expect`'s check in `read_eval_loop` never sees it, and the
file just fails normally, as if `expect` had not been used. Concretely,
this rules out using `expect` to test that closing a `let`/`pick`/`proof`
block is correctly rejected (see `doc/kurt-soundness.md` §2 for exactly
this case) — those still need the older `;;; ` marker convention.

## 10. Session toggles and output

    format sexpr | normal | original | latex   ; how formulas are printed: (and A B), or A and B, ...
    verbose on | off              ; print extra detail about *why* a match succeeded
    hint on | off                  ; reserved for future use — currently a no-op
    calc on | off       ; auto-simplify `+`/`-`/`*`/`/`/`^` on int/float literals before checking

Each, called with no argument, reports its current setting instead of
changing it. `calc on` simplifies `+`/`-`/`*`/`/`/`^` on numeric literals
(e.g. `1 + 1 = 2` becomes `2 = 2` before checking, once `load equality` and
`infix "+" ...` make `+`/`=` available at all) — no symbolic simplification,
and no explicit handling of floating-point precision (e.g. `0.1 + 0.2 = 0.3`
compares the raw Python float result, with no tolerance; an exact integer
division like `6 / 2` stays the integer `3`). With `calc on`, a comparison of
two numeric literals (`=`, `≠`, `<`, `<=`, `>`, `>=`, e.g. `3 <= 4`) is also
proven directly "by calc", and a claim follows "by calc" from a fact that
computes to the same thing (e.g. `x = -25` from `x = (-5) * 5`). Results of
substitutions (`sub`, as in `induction` or `equal-elim`) are computed too:
substituting `k + 1` into `$x + 1` gives `k + 2`, not `k + 1 + 1`. What
`calc` does not do is compute while *matching* an axiom's pattern: `$n! = $n
* ($n-1)!` at `$n=1` needs `(1-1)!` to match `0!`, which it doesn't — see
`proofs/arithmetic/factorial-recursion.kurt` for the workaround (derive the
literal equality, like `1-1=0`, as its own fact). Since `calc` also
simplifies what you type, a fact like `8 = 2^3` can't be stated with `calc
on` (it would become `8 = 8`); switch it on only where you need it, as in
`proofs/arithmetic/solve-math-equation.kurt` — it is a single global toggle,
not scoped to the current block. `hint` exists
and can be toggled but, as of this writing, nothing reads its value yet.

`help` prints Kurt's own one-line description of every keyword.

## 11. Known gaps (so you don't mistake them for bugs in your proof)

- Derivation is single-hop (§6.1) — chain several `A implies B` facts
  manually, one derived line at a time. The one partial exception: two
  facts using operators from the same declared `chain` (§4.6) combine
  automatically in one step (`$a < $b` + `$b < $c` → `$a < $c`, etc.,
  including `implies`/`iff` chains) — but that's still exactly one
  combination, not arbitrary-length automatic chaining.
- `and-elim` needs `load prop` (or a manual axiom instance) — it is not
  hard-coded the way `and-intro` is (§8.1).
- A custom `brackets` pair does not disappear the way `(` `)` does — it
  stays a real operator, printed as e.g. `[]`/`{}` in s-expression form
  (§4.2).
- `inspect` is listed by `help` but not implemented yet (raises
  `NotImplementedError` if used) — it's meant to eventually stop a running
  file and drop into the interactive shell at that point.

- In a pattern like `sum $i ($a, $b) $T`, a non-boolean schema variable
  (`$T`) can't stand for a term that depends on the bound variable `$i`
  (only a boolean `%A` can), so there is no way yet to state an axiom about
  sums of an arbitrary summand — `proofs/natural-numbers/gauss.kurt` states
  its sum axioms for the summand `$i` itself.

See `todo-claude.md` for a fuller, implementation-referenced list of
what's missing and what's feasible to add.
