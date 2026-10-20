# The Kurt Programming Language Reference

**Author:** Stefan Harmeling (implementation); this reference rewritten 2026-09-04 to match the current behaviour of `src/kurt/kurt.py`.

---

This is a reference for the current behaviour of Kurt: what each keyword
does, what the grammar allows, and what is and isn't checked. It describes
things as they are, not as they're planned to become — see `dev-notes.md` for
the history of *why* things ended up this way. The logic itself -- which symbols are variables,
when a line follows, what a block proves, what crosses a file boundary, who may postulate -- is
specified in `kurt-spec.md`, short and normative. To actually learn Kurt hands-on, start with
`keywords/00-true.kurt` and work through the numbered lessons instead; this
document is for looking things up once you already know roughly what you're
looking for.

Every claim below was checked against the interpreter while writing this
document (`kurt <file>.kurt`, or `kurt` interactively), not just read out of
the source.

## 0. The goal of Kurt

Lean, Isabelle, Coq, Mizar, Metamath and the rest exist to formalize
substantial mathematics: large libraries, strong automation, decades of
engineering behind each. Kurt isn't trying to do that, and measured against
that goal it looks small on purpose, not unfinished. It was designed for a
different goal: a student learning to prove things should get the same
fast, specific, automatic feedback that a test suite gives someone learning
to program. A proof is a text a person can read -- one claim per line, no
tactics or rule names to learn, and each line carries the reason the checker
found for it, immediately.

That goal is also why Kurt's search only ever finds and reports *one*
inference step per line (§6.1), rather than letting a tactic or an automated
solver jump from premises to a conclusion in one call. A tactic that closes
a goal in one step can save real work, but it also hides the steps it took
-- the file no longer contains them for a reader to check. Writing out every
single step is slower, and that's the point: it's the same discipline as
refusing to write "clearly" or "it follows that" in a proof on paper, and
it's where whatever understanding a proof is supposed to produce actually
happens. Kurt is built to make that slower way of proving the easy, checked
default, not an inefficiency to automate away later.

The price is real and stays real: no large library of already-formalized
mathematics, and limited automation. The kernel itself (`doc/kurt-kernel.md`
§7) is independent of the *search's reasoning* -- unification, substitution,
alpha-equivalence and binder handling are separately implemented in the
kernel and cross-tested against the search's versions -- but both still call
the same parser, and the same `flat`/`sym`/`calc` rules for when two terms
count as equal. A bug in either of those would fool the search and the
kernel identically, which the kernel's own independent checks can't catch.
Metamath's and HOL Light's kernels keep that part inside (or checked by)
their own minimal trusted core instead, so it isn't shared with whatever
found the proof. That trade was made for the teaching goal above, not as a
stage on the way to becoming a system like those. Whether the same
readability also matters for proofs a language model produces, which a
person still has to understand, is a separate, open question.

## 1. Running Kurt

    kurt                        # start the interactive shell (a REPL)
    kurt path/to/proof.kurt     # check a proof file, then exit
    kurt -i path/to/proof.kurt  # check the file, then drop into the shell (after an error: at the failing line)
    kurt -d path/to/proof.kurt  # also print debug information
    kurt -v                     # show the version (also `-V`, `--version`)
    kurt -p DIR path/to/proof.kurt   # also search DIR for `load`ed theories
    kurt -s path/to/proof.kurt       # strict, for grading (see below)
    kurt -a path/to/proof.kurt       # all errors, not only the first (also `--all-errors`, see below)
    kurt --budget 10 path/to/proof.kurt  # at most 10 s of search per line (see below; by default no limit)
    kurt -r N path/to/proof.kurt     # set the comment/reason column to N (default 42)
    kurt --no-kurtc path/to/proof.kurt   # neither write nor use `.kurtc` files (see below)
    kurt path/to/proof.kurtc             # the certificates of proof.kurt, readable (see below)
    kurt --deps path/to/proof.kurt       # the files it loads, and their certificates (see below)
    kurt --json path/to/proof.kurt       # the result as JSON, for graders and editors (see below)
    kurt --unused path/to/proof.kurt     # check, then name the lines of the proofs that nothing cites (see below)
    kurt --foundation path/to/proof.kurt # check, then show what each of its facts rests on: axioms, definitions, todos (see below)
    kurt --latex path/to/proof.kurt      # the checked file as a document, proof.tex (also --markdown: proof.md; see below)
    kurt --lean path/to/proof.kurt       # ... as a Lean 4 file, proof.lean (a prototype; see below)
    kurt --lean proof.kurt -o -          # -o FILE: to FILE instead, -o -: to the standard output
    kurt --no-line-numbers proof.kurt    # the output without the source line numbers in front
    kurt --lsp                           # a language server for editors (see below)

**In the browser:** the playground, [www.kurt-lang.org](https://www.kurt-lang.org), runs the same
Kurt, checked as you type, with the tutorial, the keyword lessons, the exercises, the theories and
the proofs of a lecture in its menus. A link can open one of these files:
`https://www.kurt-lang.org/#file=` followed by its path in the playground, e.g.
`#file=exercises/01-knights-and-knaves/2-two-islanders.kurt`,
`#file=tutorial/02-prove-an-implication.kurt` or `#file=theories/set.kurt`; it shows the
file's current version, and an exercise loads its scene. "Copy link to this proof" (in the menu
File) gives such a link for a file opened from a menu, as long as it is unchanged; for an edited
one, the link contains the text itself.

If no filename is given, Kurt starts the shell directly. If a filename is
given without `-i`, Kurt checks the whole file, prints `Proof checked` (or,
if any `todo`s are left, `Proof almost checked: N todos.` plus a list of
where they are) and exits with code `1` if checking the file raised an
error (`0` otherwise) — so a script (CI, an autograder) can tell a failed
check from a successful one without scraping stderr text. Leftover `todo`s
still exit `0` (a `todo` is a deliberate, self-reported placeholder, not a
failure), and errors raised only while typing at an interactive shell
session don't affect the exit code either.

**All errors (`-a`/`--all-errors`):** by default, a check stops at the first error. With `-a`,
it goes on after an error in the checked file, so it finds all errors that don't depend on each
other; each is printed when it is found, the lines after it get their reasons as usual, and the
file ends with `Proof not checked: N errors.` (exit code `1`). To go on, Kurt does internally
what a student would do to get past the error -- the file isn't changed:

- a formula that can't be derived is admitted, as `todo` would (so the lines that use it don't
  fail because of it);
- a block that doesn't close -- a proof whose goal isn't reached, also at the end of the file --
  is closed anyway, and its claim counts as admitted (any other block is discarded, as `break`
  does); the line that closed it is then checked on its own;
- a claim without a proof counts as admitted;
- any other line (one that can't be read, a wrong use of a keyword, a type error) is dropped, as
  in the shell; if it opens a block, the block is skipped too, and so is the `proof` of a `show`
  that can't be read. A dropped line may cause later errors (e.g. a `def` that failed).

The admitted lines are errors, not `todo`s: they aren't listed as `todo`s, the file gets no
`.kurtc`, and the result is failed. Some errors still stop the check: an error in a file it
loads (and on a `load` line), anything inside an `expect` block (there the error is the expected
result; §9.6), and a `KernelError`. The editors (`kurt --lsp`) and the playground show all errors
by default; from Python, `kurt.RunConfig(all_errors=True)`, and `CheckResult.errors` lists them
(`error` is the first one).

**Budgets (`--budget SECONDS`), and cancelling a check:** the search for one line normally takes
a fraction of a second, but a false claim among many facts can take minutes (the search tries
every combination before it gives up). A budget stops it: `kurt --budget 10 proof.kurt` allows
each line 10 s of search; a line that takes longer fails with a `ResourceError`:

    ResourceError: the search for this line stopped after 10 s, its budget -- the line is
    neither proved nor refuted; a larger budget may decide it (...)

It is a kind of its own, apart from a `ProofError` (a rejection): the budget says nothing about
the line, only that the search didn't finish. A budget never changes which steps are accepted --
it only stops the search early -- and the kernel isn't involved. With `--all-errors`, the check
goes on after it as after a `ProofError` (the line is admitted, see above); `expect` can't name
`ResourceError` (as it can't name `KernelError`), so a proof file can't depend on a budget, and an
`expect "ProofError"` whose line runs out of budget is an error, not confirmed. The command line
has no budget unless `--budget` says so; the editors (`kurt --lsp`) allow 30 s per line (the
initialization option `budget`, 0 for none), the playground the same, and
`scripts/grade_exercise.py` too (`--budget SECONDS`). The budget applies to every line checked,
also in the files a proof loads.

From Python: `kurt.RunConfig(time_limit=10)` (seconds), `kurt.RunConfig(step_limit=5000)` (steps
of the search: a goal against one fact, or a premise against the facts -- about 1000 to 4000 a
second, the same on every machine), or both; `CheckResult.exhausted` says that a line's budget was
used up (its `errors` entry has the kind `ResourceError`), and so does the JSON of `--json`.
`kurt.RunConfig(cancel=f)` asks `f()` at every step and every line, and stops the check with a
`ResourceError` at the current line when it returns true (`CheckResult.cancelled`; the lines after
it are not checked, also with `all_errors`) -- e.g. `cancel=event.is_set` for a `threading.Event`
another thread sets. The language server uses it to stop the check of a text that was edited
meanwhile (before, the check of the new text waited for it).

**Progress, from Python:** `kurt.RunConfig(progress=f)` calls `f` with a dict when a file starts,
at each of its statements and when it is done: `file`, `line` (of `lines`), `index` of `files`
(the files checked so far -- a theory that the session has checked before and that didn't change is not
checked again) and `done`. The playground shows it as a progress bar.

**Strict mode (`-s`/`--strict`), for grading:** the checked file (and any
file it loads that isn't trusted) may not contain `use` or `todo`, a `chain`
there needs its rules proved before it (§4.6), and every symbol must be declared before its use (§3.2), and `calc` may not bind symbols to the calculator — everything has to be proven from the theories that come with Kurt, or
from the ones found in a `-p DIR` directory (e.g. an exercise's axioms, as
given by the teacher). Those are the *trusted* theory files; `use` inside a
`sandbox` or `expect` stays allowed, since their content is discarded. It
is a command-line switch rather than a statement in the file, so that the
file being graded can't switch it off.

**Certificates of a file (`.kurtc`):** after a file checks completely (no error, no `todo`), Kurt
writes `foo.kurtc` next to `foo.kurt` (if the directory is writable) -- the certificates of its
claims (§6.5), in JSON, with the hash of the file and the files it loads. When `foo.kurt` is
checked or loaded again, unchanged, each claim first tries its stored certificate: rebuilt with
the facts as they are now (a step of the line itself that it cites, `17a`, from its own stored
certificate first), and checked by the kernel; only if that doesn't work, Kurt searches
as usual. So the output is the same, it is just faster (for the proof files of this repository,
up to five times). A `.kurtc` can't make Kurt accept anything the kernel doesn't check -- a wrong
or outdated one only costs the time of the search -- so it is also used with `--strict`. Kurt
writes and uses `.kurtc` files when run as `kurt` (the command line or shell); from Python, only
in a session with `kurt.RunConfig(kurtc=True)` -- for a text (`check_text`), only for the files it
loads, not for the text itself. `kurt --strict foo.kurtc` checks `foo.kurt` with the same options
as `kurt --strict foo.kurt`.

The theories that come with Kurt come with their certificates: the package has them next to the
theories, and the single-file `kurt.py` embeds them (`scripts/build_certificates.py` makes them).
In them, a theory of Kurt is named `<kurt>/propositional.kurt`, not by where it is, so they fit wherever
Kurt is installed. If a theory's directory isn't writable, its new certificates go to the cache
directory (`$XDG_CACHE_HOME/kurt`, or `~/.cache/kurt`). A `.kurtc` that is up to date isn't
written again. (Without them, `load rational` in the single-file `kurt.py` took 8 s each time,
1.2 s with them.)

`kurt --json foo.kurt` checks the file and prints the result as JSON (exit code as above): `ok`,
`complete` (also no `todo` left), `error`, `error_kind`, `error_line`, `failure` (why a step
failed, §6.1), `errors` (each with its `kind`, `line`, `column`, `message`, `failure`, and the
`file` for an error in a file it loads; with `--all-errors` all of them, else the one), `exhausted`
and `cancelled` (a budget was used up, the check was cancelled; see above), `todos`,
`loaded` (the files it loaded, also through other files), `certificates` (of each line, as `cert` shows them), the text `output`, and `events`, each printed line as a record -- the
source `line`, its `id` (`5`, `5a`, `11-13`), its `kind` (`step`, `claim`, `open`, `close`,
`assumed`, `load`, `declaration`, `expect`, `error`, `text`, `other`), `level`, `text`, the
`rule` and the lines it `uses`, its `label`, the user's `comment`, and where they apply its
`steps` and `schema`:

    {"line": 5, "id": "5", "kind": "step", "level": 0, "text": "B", "reason": "5 by rule(4)",
     "comment": "modus ponens", "rule": "rule", "uses": ["4"]}

From Python, the same comes from `kurt.check_file(path)` or `kurt.check_text(text)` (a
`CheckResult`, with `.events` and `.to_json()`). A text is never trusted (under `strict`, it may
not `use`), whatever name it is given -- trust comes from where a file is read. One exception, for
the editors: a text under the path of a theory of the running Kurt that is exactly that file's text
(saved, unchanged) is that theory, trusted like it; a changed text is not. Like the command
line, the module refuses to check under `python -O` (which removes Kurt's internal checks).

**Does the file prove a given theorem?** `ok` and `complete` say that the file checks (an empty
file is complete), not what it proves. `result.proves(statement, label=None)` says whether the
file proves `statement` at its top level: derived in this file by steps that rest on no
admission -- not a `use` or `def`, not a `todo` or a claim whose proof contains one (anywhere
in the proof, needed or not) or uses a fact that was admitted (a `todo F` before it, a claim
admitted after an error with `--all-errors`), not a fact of a loaded file, not a claim that is
withdrawn (`break`) or only proved inside a block. With `label` (or a label written in the
statement, `proves('A ⇒ B "ab"')`), the fact must carry that label; without one, any label
will do. The statement is written as Kurt reads it, with or without `show`, and is read in the
file's final context: `A ⇒ B` and `A implies B` are the same statement, `A ∧ B` and `B ∧ A`
too (`∧` is `sym`), and a statement the file can't read (a notation it doesn't declare) is one it
doesn't prove. `result.proof_of(statement, label=None)` says how the file states it:
`'proved'`, `'admitted'` (a `todo`, or a proof that rests on one or on an error), `'assumed'`
(`use`, `def`), `'loaded'` (a fact of a file it loads, not proved here), or `None` (not stated
at the top level); when it is stated more than once, the best counts. `result.loaded` lists the
files the check loaded, directly or through other files, by their paths -- a grader checks it
against the files a solution may load (`scripts/grade_exercise.py`: only what the exercise
loads; a file that states the answer is no proof, even if the solution derives the answer from it
in one step). Neither says anything after a check that stopped at an error (`proves` is false,
`loaded` empty); with `all_errors`, the check runs to the end, and `proves` tells the claims
whose proofs are sound from the ones admitted after an error.

    >>> result = kurt.check_text('load propositional\nbool A, B\nshow A ∧ B ⇒ A "a"\nproof\n    assume A ∧ B\n        A\nqed\n')
    >>> result.proves('(A and B) implies A'), result.proves('A ∧ B ⇒ A', 'b'), result.proof_of('A')
    (True, False, None)

**What a fact rests on (`--foundation`).** `kurt --foundation foo.kurt` checks the file and then
shows, for each fact at its top level that is labelled or proved, its class -- `axiom` (`use`),
`definition` (`def`), `todo`, or `theorem` (a proved line, or a `show` with its proof) -- and, for a
theorem, what it rests on: the `use` axioms and `def`s that the steps of its proof cite, directly
or through the facts they cite, by file; the `todo`s that admit a step; the steps computed by the
calculator (`calc on`), with the symbols' bindings (`` `+` add``). Found by walking the certificates of
the steps (§6.5): through the blocks (a block's result rests on what its last line rests on; the
block's own assumption is discharged when it closes, so it is no postulate), and into the theories
it loads (a loaded theorem brings what it rests on in its file). A theorem with no `todo` behind it
is *established, relative to* these axioms and definitions; one with a `todo` (or, with
`--all-errors`, a line admitted after an error) is *accepted relative to* it. The class of a fact
stays what it is (§6.3.1): `use` is an axiom, also where it could be proved. After the facts, the
reverse: each postulate with the facts that rest on it -- for a change of an axiom, this is who is
affected. For a teacher choosing a trusted set of theories: which `use`s a theorem really needs.

    gauss.kurt: what each fact at its top level rests on

    "gauss" (line 12, theorem): established, relative to 4 axioms, 1 definition and the calculator
        gauss.kurt: "sum-def" (line 5), line 14 computed by the calculator (`+` add, `=` eq)
        natural.kurt: "induction" (line 40), "plus-zero" (line 22), ...
        equality.kurt: "equal-elim" (line 23)

    each postulate, and the facts above that rest on it:
        ...

The rules a `chain` declaration stands for appear as `` the rules of `chain = < <=` ``. From Python,
`check_file(path, foundation=True)` (and `check_text`) fills `CheckResult.foundations`, one record
per fact -- `label`, `line`, `file`, `text`, `class`, `status` (`established`/`accepted`, or the class
of an axiom, definition or `todo`) and `rests_on`, each postulate with its `kind` (`use`, `def`, `todo`,
`calc`, `admitted`), `file`, `line`, `label` and `text` -- and `result.foundation("gauss")` finds one by
its label (or line); `kurt --json` includes them as `foundations`. Nothing is stored for this: it is
computed from the certificates after the check, so it costs nothing where it isn't asked for.

`kurt --lsp` is a language server (the Language Server Protocol, over
stdin/stdout) for editors -- VS Code (the extension of kurt-syntax), Emacs
(Eglot), and Neovim. A file is checked when it is opened and saved. A client
can request debounced checks while typing. Errors and `todo`s appear as
diagnostics at their lines, the reason of each checked line appears at its end
(an inlay hint) and on hover; what a line prints besides a reason (`builtin`, `infix`,
`theory` without arguments, `cert 14`, ...) appears on hover too (its first 60 lines); a line
without a certificate says on hover what it does, with its own symbols (`var a, b`: "`a`, `b`
stand for anything ..."; `infix ^ 75 74`: right-associative; `calc on`, `tex`, ...). A line
inside a proof that nothing cites is greyed out (a hint with the LSP tag "unnecessary", as an
unused import), and `kurt --unused` names these lines: backwards from what must stay -- the
top-level lines, the labelled ones, `qed`, and a proof's last line that is its goal -- along what
each step cites; a block's result cites the block's last line and its first, so a block whose
result nothing needs is greyed out entirely. A line that restates a block's result (`∀ x Q(x)`
after a `let` block), an assumption, or the line before it isn't greyed out: it helps the reader,
and the hover says that Kurt doesn't need it. Only lines of `proof`, `assume`, `let`, `pick` and
`case` blocks are reported, and only of a file without errors; "nothing cites it" isn't "it could be
deleted" (a step may be found without citing a line that helped). And
completion knows the state at the cursor (the
next step, the value after `=` with `calc on`, LaTeX shortcuts, theories, and
names). Positions use the LSP's UTF-16 convention, so mathematical symbols
before a completion or hint do not shift it.

The initialization options are `theoryPaths` (additional trusted theory
directories), `strict`, `allErrors` (all errors of a file, the default; `false`:
only the first, as `kurt` without `-a`), `budget` (seconds of search per line, 30 by
default; 0 for none; a line that takes longer gets a `ResourceError` diagnostic, see
"Budgets" above), `checkOnChange` (also accepted as
`checkOnType`), and `checkOnChangeDelay` in seconds. A check of a text that is edited while it
runs stops at its next step. The directory of the edited file is searched
first but remains untrusted; only an explicit theory path grants trust. When an
open document loads another open document, Kurt checks the current unsaved
text of the loaded document. Closing a document clears its diagnostics.

`kurt --deps foo.kurt` shows the tree of the files that `foo.kurt` loads (read from their `load`
lines, before anything is checked), each with the state of its certificates and the dates of the
file and its `.kurtc`:

    gauss.kurt  -- certified  (file 2026-09-29 06:11, certificates 2026-09-29 06:13)
    └─ analysis.kurt  -- certified  (file 2026-09-28 16:11, certificates 2026-09-29 06:13)
       └─ natural.kurt  -- out of date: the file changed since  (file 2026-09-29 07:02)
          ├─ set.kurt  -- certified, but logic.kurt changed since  (...)
          ...

"certified, but ... changed since" means: the certificates fit the file, but a file it loads has
changed -- they are still tried (and checked by the kernel) the next time, and rewritten after it.

After the tree, `--deps` checks `foo.kurt` (quietly) and lists the symbols it uses from theories
that it doesn't load itself, by theory -- e.g. `logic.kurt: \`forall\`` for a file that loads
only `natural` and writes `∀` (see `load`, §8.2).

**The `.kurt` file is the only source of truth.** Everything else is derived from it, can be
deleted, and is never trusted: a `.kurtc` only holds hints, which the kernel checks each time;
the reasons Kurt prints and `cert` only show a check that already happened; and `save` writes
Kurt source again, not a snapshot of facts.

`kurt foo.kurtc` shows the certificates of `foo.kurt`, line by line, as `cert` does: the goal, the
rule (with its file and line), the values of its variables, and the facts it uses, and the
blocks it closes. Kurt checks `foo.kurt` for that (quietly, with the `.kurtc`), so what is shown
was checked by the kernel; the first line says whether the `.kurtc` still belongs to the file.


**Documents and Lean (`--latex`, `--markdown`, `--lean`, `-o`).** A checked proof as a document: `kurt --latex proof.kurt` writes `proof.tex`, `kurt --markdown
proof.kurt` writes `proof.md` -- each line in mathematical notation, indented by its block, with its
reason, and then the certificates. A line that continues a chain is written as in mathematics, its
relation and its right side (`= x`), without the left side Kurt repeats. How a symbol is written comes from its theory:

    tex alpha \alpha                    ; a symbol
    tex sum \sum_{$1=$2}^{$3} $4        ; $1, $2, ... the places of the arguments, in the order of
                                        ; the shape (`arity sum _ (_, _) _`: the variable, a, b, T)

(only output: nothing Kurt checks changes; exported with `load`). Without a declaration, Greek
letters and symbols are written by their LaTeX names, longer names upright (`\mathrm{abs}`), and a
variable `$x` as `x` -- as `\mathsf{x}` only where a constant `x` is in the same formula.

A Lean 4 file of a checked proof (a prototype): `kurt --lean proof.kurt` writes `proof.lean`
(it doesn't run Lean; the last line Kurt prints is the command for that), and `lean proof.lean` checks it again
with Lean's kernel. It writes each step from its certificate -- the rule with the certificate's
values, and its premise from the cited facts -- and the theories' rules as Lean `axiom`s (but
those with a proof in Lean, see below), so Lean checks the proof, not the theories. Kurt's objects are one type `Obj`, its statements `Prop`; a
`flat` or `sym` operator comes with its associativity or commutativity as an axiom (that is what
the declaration asserts), `∀ x ∈ A P` is `∀ x, x ∈ A → P` and `∃ x ∈ A P` is `∃ x, x ∈ A ∧ P`
(§4.4's "forall-cond-def"/"exists-cond-def"), any other binder is a constant applied to `fun x =>
...` (`sum i (a, b) T` is `sum a b (fun i => T)`; logic.kurt's `∃! x P(x)` is what its definition
says, `∃ x, P x ∧ ∀ y, P y → y = x`, by its `lean`), a `def` is a Lean `def` with its defining
equation proved by `rfl` (a `def` over a tuple, `def coprime($a, $b) ⇔ ...`, a function of the
components, `coprime a b`; the `def`s of the symbols in what a step cites of a loaded file are Lean
`def`s too), a `case` step `rcases`, and a symbol that is applied and also an object (`f a`, `f ∈ (A
→ B)`) is an `Obj` applied with `k_apply`. Without a number theory, a number is a constant of its
own (`k_num_17 : Obj`; `0` and `1` of field.kurt are its zero and one, which only its axioms
describe -- Kurt knows nothing else of them there), and a `calc` step is not translated: a `sorry`,
listed at the end of the file. The rules of propositional.kurt, logic.kurt and equality.kurt are theorems
of Lean's logic (each `lean "label" grind`, see below; `invimplies` by its `lean`), so Lean checks the
logical rules a proof uses, with or without Mathlib.

*With Mathlib (numbers).* A theory says how its symbols read in Lean (with Mathlib, but for
propositional.kurt's `lean invimplies ($2 → $1)` and logic.kurt's `∃!`), as `tex` does for LaTeX (raw to the end of the line, `$1`, `$2`, ... the places of the arguments; one template
per number of arguments, so `-` has two; only output, exported with `load`):

    lean Obj ZFSet                      ; the Lean type of Kurt's objects (objects.kurt)
    lean real ℝ                          ; the Lean type of the sort `real` (numbers.kurt), embedded into it
    lean + $1 + $2
    lean - $1 - $2                      ; `a - b`
    lean - -$1                          ; `- a`
    lean - opaque $1                    ; `- a` has no Lean meaning here: a constant of its own
    lean ! Real.Gamma ($1 + 1)
    lean Nat member $1 ∈ Set.range (fun n : ℕ => (n : ℝ))     ; what `x ∈ Nat` means
    lean {_,...,_} k_numset (fun x_ => ∃ k_ : ℕ, x_ = $1 + k_ ∧ x_ ≤ $2)   ; a set with `...`, by its shape
    lean lim (Filter.limUnder (nhdsWithin $1 {$1}ᶜ) $2)        ; a binder: `lim v a T`

A `lean` declaration replaces the one of a file it loads (for the same number of arguments). A
binder's places are its condition (if it has one) and its body, both as functions (`fun x => ...`),
and the arguments between them, a range `(a, b)` as two (`sum i (a, b) T`: `$1` a, `$2` b, `$3` the
body). `member` declares a set of numbers: a definition, the set of the embedded numbers with the
property (`k_numset`), and what membership in it means a theorem (`k_mem_Nat : ∀ x : ℝ, k_emb x ∈
Nat ↔ x ∈ Set.range ...`) -- from it the rules about the set are theorems. A set written with `...`
has the `lean` of its shape, `{_,...,_}` for `{a, ..., c}`, `{_,_,...}` for `{a, b, ...}` (the places
are its elements).

*A model of a theory's own operations.* `lean SYMBOL def TEMPLATE` makes the template a Lean
definition (`@[irreducible] noncomputable def`, named by the symbol and the number of arguments),
and the terms use its name -- they stay small, and the laws of a `flat`/`sym` operator are proved by
unfolding it. A numeral can be mapped like a symbol (`lean 0 ...`) where no theory of numbers gives
it a type. field.kurt is the example: `K` is the set of the embedded reals, and the operations decode
their arguments (`k_dec`, the inverse of `k_emb`), compute in ℝ and embed the result:

    lean K def ZFSet.range (fun x : ℝ => k_emb x)
    lean 0 k_emb (0 : ℝ)
    lean + def k_emb ((k_dec $1 : ℝ) + (k_dec $2 : ℝ))

modal.kurt has a model of its own as the objects (`lean Obj ((Nat → Nat → Prop) → Nat → Prop)`,
Kripke semantics): `kurt --lean field.kurt` and `kurt --lean modal.kurt` prove every axiom of the
theory true in its model (doc/kurt-soundness.md §11).

*Sets and numbers.* Kurt's objects are the sets of Mathlib's model of ZFC (`ZFSet`, objects.kurt's
`lean Obj ZFSet`), and a sort with a type of its own -- numbers.kurt's `lean real ℝ` -- is embedded
into them, as `real ⊂ set` says: `k_emb : ℝ → Obj` is a definition (an ordinal for each real, by a
well-ordering, and its von Neumann level), injective by Mathlib's theorems, so nothing is assumed.
A variable, constant or binder of the sort `real` is a real (`∀ x ∈ Nat` over `ℝ`, `x` a number by its places or `default real`),
every other object a set; a number at the place of a set is `k_emb x` (`1 ∈ A` is `k_emb 1 ∈ A`,
`{1, 2}` Lean's own `{k_emb 1, k_emb 2}`, `(1, c)` the Kuratowski pair `ZFSet.pair`), and `=`
between a number and a set compares them as sets. In set.kurt `∈` is `ZFSet`'s membership, `∅`,
`∪`, `Pow`, `×`, `A → B` (`ZFSet.funs`) Mathlib's, `{z ∈ A | P}` separation (`ZFSet.sep`; a part
chosen among the numbers, `{n ∈ Nat | n > 2}`, with the property read on the embedded numbers,
`k_lift`), a mapping applied, `f a`, the `b` with `(a, b) ∈ f` (`k_apply`, a choice), and every rule
of set.kurt, its theorems and the rules of a set by its elements (`$x ∈ {a, b, c} ≡ ...`) are
theorems of Mathlib. So a proof that mixes sets and numbers is checked against one model of both --
no axiom of set.kurt is read over the reals. The rules of propositional.kurt, logic.kurt and equality.kurt
are proved once for every type (`∀ {α : Type u}`: their variables without a sort), so "forall-elim"
applies to `∀ x ∈ Nat` over the reals and to `∀ x` over the sets alike. Without set.kurt and the
numbers (field.kurt, group.kurt, vectorspace.kurt: no sorts), the objects stay an opaque `Obj`.

The theories of numbers all read Kurt's numbers as Mathlib's reals `ℝ` (numbers.kurt's `lean real
ℝ`; natural.kurt, integer.kurt, rational.kurt extend it, as in Kurt): `Nat`, `Int`, `Rat` are the
sets of the embedded casts of `ℕ`, `ℤ`, `ℚ`, so `-` and `/` are the real ones everywhere, `^`
is the real power `Real.rpow`, and `n!` is `Γ(n + 1)` (`Real.Gamma`: `0! = 1` and `n! = n (n -
1)!` for every `n > 0`, the two rules numbers.kurt has, and the factorial for a natural number). In
analysis.kurt `abs` is `|x|`, `sum i (a, b) T` the sum of `T(b), T(b-1), ..., T(a)` (`⌈b - a⌉ + 1`
terms; for fewer than none, its negative, as for a sum over an integer range: so "sum-last" holds
for any `a`, `b`), `max`/`sup` the supremum `sSup` of the values (`min`/`inf`: `sInf`), `argmax` a
choice (Hilbert's ε), `lim` and `tends` Mathlib's limit along the punctured neighbourhoods; in
continuity.kurt and derivative.kurt `cont`, `diff`, `deriv` are `ContinuousAt`,
`DifferentiableAt`, `deriv`; in sequences.kurt `converges` and `seqlim` the limit along `atTop` of
the values at `0, 1, 2, ...`; in integral.kurt `integral` is Mathlib's interval integral and
`integrable` is read as "continuous on [a, b]" (the rules make a function integrable only that way).

*The theories' rules are theorems.* A rule's proof in Lean is kept with the rule, in its theory:

    use $a = $b  ⇒  $a + $c = $b + $c   "add-eq"
    lean "add-eq" intros; subst_vars; rfl

`lean "label" TACTIC` is a line of a proof (a tactic, raw to the end of the line, `;` too, so no
comment after it; more lines for the same label are the next lines of the proof, an indentation
after one space is kept) of the fact "label" of the file, at its top level and after the fact --
only output, as `tex`: Kurt doesn't read the tactic. `kurt --lean` writes such a rule as a
`theorem` with this proof instead of an `axiom` (with a comment `-- numbers.kurt:70 "add-eq":
proved in Lean`), so Lean checks the theory's rules, not only the steps of the proof; a tactic that
doesn't prove the rule is an error in Lean. The rules a `chain` of Mathlib's relations generates
(`chain = <= <`: "chain-trans-1-2") are theorems by `linarith`, as `flat`/`sym` of `+` are by `ring`,
and what the calculator knows of `Nat` (`6 ∈ Nat`, `k_calc_Nat`) is one of `k_mem_Nat`; a `def` of a
loaded file that a step uses is a Lean `def`, as the file's own. Every rule of the theories of
numbers (numbers, natural, integer, rational, analysis, continuity, sequences, derivative,
integral) and of set.kurt is proved this way -- natural.kurt's six rules of `{a, ..., c}` and `{a, b,
...}` too (the sets of their shapes' `lean`) -- but "integral-riemann" (true for a continuous
function, but its proof isn't in Mathlib); and the theorems Kurt proves in natural.kurt,
integer.kurt and rational.kurt have a `lean "label"` too, for a proof that cites them (those about
`⊂`, `even`, `odd`, `∣`, `coprime` unfold the `def`s of these symbols). The tactics don't name the variables (`intros`, `‹_›`):
Kurt orders the arguments of `+`, `*` and `∧` its own way, and names its variables by numbers.
`kurt --lean numbers.kurt` writes a theory itself, all its rules with their proofs.

Where the proof's theories give a `lean Obj`, `kurt --lean` writes `import Mathlib`, `abbrev Obj :
Type 1 := ZFSet.{0}` with the embedding instead of the opaque `axiom Obj : Type`, a number `2` as `(2 : ℝ)`, a mapped symbol by
its template (the others stay `axiom`s), the laws of a mapped `flat`/`sym` operator as theorems
(`ring`), and a `calc` step by `norm_num` (then `simp`, `ring_nf`, `linarith`, `decide`; for a fact
that computes to the goal, the same on the fact and the goal) -- what none of them closes stays a
`sorry`, which Lean reports. The last line Kurt prints is then `lake env lean FILE`, to run in a
lake project with Mathlib. Kurt's repository has one, `scripts/lean` (Lean and Mathlib of the same
version as `scripts/lean-toolchain`; neither Kurt nor `pip install kurt-lang` needs it):

    cd scripts/lean && lake exe cache get      # once: Mathlib's prebuilt files, ~5 GB in scripts/lean/.lake
    python3 scripts/lean_check.py proof.lean   # Lean with Mathlib if the file imports it, else plain `lean`

`-o FILE` writes the document (or the Lean file) to `FILE` instead of next to the proof, `-o -` to
the standard output, for a pipe: `kurt --lean proof.kurt -o - | lean --stdin`, `kurt --markdown
proof.kurt -o - | pandoc -o proof.pdf`. Then what Kurt says goes to the standard error, and a proof
that doesn't check writes nothing (an error, exit status 1). With `-o`, one format per run
(without it, `--latex --lean` writes both files).

## 2. Lexical structure

Kurt reads a proof one *statement* at a time; a statement occupies one or
more physical lines (see §2.1 on indentation/continuation).

- **Comments** start with `;` and run to the end of the line. They are
  ignored completely -- a label is written as a string instead (§6.2). A
  line with nothing but a comment is skipped like a blank line, whatever
  its indentation.
- **Symbols** (identifiers) are `[A-Za-z][A-Za-z0-9]*`, optionally followed by primes (`a'`,
  `f''`) and preceded by a single `$` or `%` (see §3.2). A Greek letter followed by digits or
  primes is one symbol too (`λ1`, `ε'`), also as a variable (`$Γ`, `%φ`, `$Γ2`). Plain
  multi-character identifiers remain ASCII; Greek letters next to each other (`αβ`) are
  individual symbols.
- **Numbers** are `INT` (`[0-9]+`) or `FLOAT` (`[0-9]+\.[0-9]+`) literals.
- **Strings** are `"..."` (no escaping of embedded quotes); used for labels
  (`use ... "my-label"`) and for some keyword arguments that take an
  operator symbol as text (`infix "+" 20 20`).
- **Operator characters.** Besides letters/digits, `(`, `)`, `{`, `}`, `[`,
  `]`, and `,` are always their own single-character symbols — they never
  glue to each other or to anything else, precisely so a custom `brackets`
  pair keeps working next to unrelated punctuation with no space (e.g. a
  trailing `...}` is two tokens, `...` then `}`, not one token that
  swallows the closing brace). A run of characters from `.:=+-*/#&^'∈!<>|_~`
  (note: no brackets in this class) glues together into *one* symbol
  instead (so declaring `!=` gives you a single two-character operator, but
  writing `!!` without spaces is one symbol `!!`, not two `!` tokens). A
  fixed set of additional Unicode symbols is recognised one character at a
  time — exactly the symbols that appear as *values* in Kurt's LaTeX-input
  table (§2.2): the common logic/set-theory symbols (`∀ ∃ ∧ ∨ ⇒ ⇐ ⇔ ¬ ⊤ ⊥ ∈
  ∉ ∋ ⊂ ⊆ ⊃ ⊇ ∩ ∪ ∖ ∁ ∅ ≡ ∘ ↦ ⇝ → ⊢ ∞ ≤ ≥ ≠ × · ∣ ⟨ ⟩ ⟂ ∼ ≈ ≺ ≼`), modal-logic
  symbols (`□ ◇`), and the Greek alphabet; `∃!` and `⁻¹` are one symbol each. **Any other non-ASCII character is a lexing error** — you
  cannot declare an operator using an arbitrary Unicode symbol that isn't
  already on this list.
- **`load` (and `list`, `tex`, `lean`) are special in the lexer.** A line starting with `load` (case
  insensitive) is scanned specially: everything after it up to a `;` or end
  of line is taken as a comma-separated list of filenames (quoted or bare),
  not parsed as an expression. This is why `load propositional, equality` and `load
  "my-theory.kurt"` both work, without `propositional`/`equality`/`"my-theory.kurt"`
  needing to be otherwise-valid symbols. `tex SYMBOL ...` and `lean SYMBOL ...` take the rest of
  the line raw, as LaTeX or Lean text (§1, documents and Lean), up to a comment; `lean "label"
  ...` (a line of a proof in Lean) takes all of it, `;` too -- such a line has no comment.

### 2.1 Statements, indentation, and line continuation

A statement can span more than one physical line: if a line ends
mid-expression, Kurt automatically treats the next line as its
continuation — no explicit continuation marker is needed.

In a *file*, indentation is significant. Opening a block (`proof`,
`assume`, `case`, `let`, `pick`, `sandbox`, see §9) requires the next line
to be indented relative to it; dedenting afterwards closes as many nested
blocks as the drop in indentation implies. A **blank line**, or a line with
nothing but a **comment**, is always safe anywhere, at any indentation,
including deep inside a nested block — it's skipped outright rather than
measured, so it never dedents anything on its own. A tab counts as four
spaces. Any other increased indentation is an error — except for the
continuation lines of a chain (§4.6).

### 2.2 LaTeX-style input shortcuts (interactive shell only)

Typing Unicode symbols is inconvenient on most keyboards, so **in the
interactive shell**, before a line is scanned, Kurt rewrites LaTeX-style
commands to their Unicode equivalent: `\forall` → `∀`, `\exists` → `∃`,
`\implies` → `⇒`, `\invimplies` → `⇐`, `\and`/`\or`/`\not` (or `\neg`)/`\iff`/`\equiv`/
`\top`/`\bottom` → `∧`/`∨`/`¬`/`⇔`/`≡`/`⊤`/`⊥`, `\in`/`\notin`/`\subset`/`\subseteq`/
`\supset`/`\supseteq`/`\cup`/`\cap`/`\emptyset`/`\to`/`\mapsto`/`\leadsto`/`\circ`,
`\times`/`\cdot`/`\mid`/`\langle`/`\rangle`/`\infty`, `\leq`/`\geq`/`\neq`,
`\box`/`\b`/`\diamond`/`\d` (modal logic), `\vdash` → `⊢`, and the full Greek alphabet
(`\alpha`, `\Gamma`, ...). The standard LaTeX names work too: `\le`/`\ge`/`\ne`,
`\lnot`, `\land`/`\wedge`, `\lor`/`\vee`, `\Rightarrow`, `\Leftrightarrow`, `\bot`. **This replacement only happens for lines typed
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
`minimal.kurt`, see §8.1), so `f x` means "`f` applied to `x`". A symbol
without an `arity` is curried: `f x y` is `f x`, applied to `y`, and `(f x) y`
is the same term -- both are stored as one call, `(f x y)` (so `f x` is no
subterm of it that a rule could rewrite). With a declared `arity` (§4.3), `f`
takes exactly that many arguments, and further ones apply to the result: with
`arity f 2`, `f x y z` is `(f x y) z`, and `(f x) y` is an error, `f x` lacks an
argument -- a forgotten argument or a misplaced bracket is caught. `f(x, y)` is
something else: `f` applied to one argument, the pair `(x, y)` (§4.3). Where a
function is applied in steps as a term of its own, as in the lambda calculus, a
theory writes application as an operator (lambda.kurt). This is also why you can write `not A` even though `not` is
declared as a `prefix` operator elsewhere — a bare `symbol symbol`
juxtaposition is space-application regardless.

Function application binds more tightly than every other operator, as in
mathematics: `f x + y` and `f(x) + y` are `(f x) + y`, and `s n in Nat` is
`(s n) in Nat`. Parentheses only group, so `f(x)` is just `f x` -- with one
difference: a bracket written directly after a symbol, without a space, makes
one term that binds more tightly still. So `inv det(A)` is `inv (det A)` (while
`inv det (A)` is `inv det A`, `inv` with the two arguments `det` and `A`), and in the
condition of a binder,
`∀ $x ∈ Perp(M) Q($x)` reads `Perp(M)` as one term.

### 3.2 Constants vs. variables

Every symbol is exactly one of:

- a **constant** — one fixed, specific object, declared with `const x`, or
  implicitly whenever it's introduced by `let`/`pick`/`def`/`brackets`, or
  the first time an otherwise-undeclared symbol is used in a formula (e.g.
  after `use P c`, both `P` and `c` are constants; `prop` only records that
  a symbol is boolean, see §5, not whether it is a constant). Such a
  first use is shown as an ordinary declaration in the output (`const P ;
  added constant`), including when the symbol already had a syntax or
  type declaration such as `infix P ...` or `prop P`. A wholly undeclared
  symbol is often a typo; with `--strict` (§1), it is an error instead. Or
- a **variable** — may stand for arbitrary objects, declared with `var x`.

Once a symbol's role is fixed *on a given level* (see §9 on blocks/levels),
it cannot be changed in either direction on that level: declaring `const x`
then `var x` fails, and so does the reverse. A symbol that is a constant
inside a block can still be an ordinary (as-yet-undecided) symbol outside
it, once the block closes and its constants go out of scope.

**How Kurt handles variables** (the design, kept as it is on 2026-10-15):

- A variable stands for anything: a `use`, `def` or `todo` with a variable
  in it is a *schema*, which the search instantiates by matching -- `use $a
  = $a` gives `c = c` for every term `c`. A variable is written with a sigil,
  `$x` for a term and `%A` for a formula -- or as a plain name declared with
  `var x`, which is the same thing in nicer clothes: the theories write `var
  n, m` and then `use n + 0 = n`, as a textbook would. Kurt shows the schema
  it reads (`; schema: ∃ z (R z $x)`), and warns when a `use` only relates
  declared variables (`use a <= b` with `var a, b` says every number is
  below every number).
- A constant stands for one object. `const c` declares it; `let x`, `pick c`
  and `def` introduce one; so does the first use of an undeclared name.
- Inside a block, a variable can be held fixed: `let $x` (or `let x` for a
  declared `var x`) makes it an arbitrary but fixed object for the block,
  and closing the block gives the `∀` (§9.2); an assumption's variables are
  fixed inside it the same way (`assume P $x`: one `$x` throughout the block).
- `load` exports no variable: a loaded file's `var n` stays its own, and its
  schemas arrive with internal variables (`$$07`), so the loader's `n` is
  free for anything. A declared `var` of the loader can't be a constant of a
  loaded file, or the other way round (§7 of doc/kurt-soundness.md).
- Variables are never a value of each other's binders: a `$T` under a binder
  over `$i` stands for a term that doesn't depend on `$i`, unless the rule
  only ever uses it under that binder or with a substitution for `$i`
  (`sum $i ($a, $b) $T`; doc/kurt-soundness.md §8.10).

The alternative -- variables only with a sigil, no `var` -- was weighed and
rejected: it would make the theories and lecture notes uglier for a tidiness
that the warning and the `; schema:` output already give.

Symbols starting with `$` or `%` are **always** variables (`const $x` is an
error) — they exist specifically to write *axiom schemas* in `use` lines,
where `$x` stands for an arbitrary non-boolean term (e.g. `use $a = $a`)
and `%A` stands for an arbitrary boolean formula (e.g. `use %A and %B
implies %A`); mixing them up is a type error (`$A implies $A`), and no
step gives a `$`-variable a formula or a `%`-variable a term as its value
(the search refuses it, the kernel checks it again). `let` fixes a term
only (`let %A` is a type error since 2026-10-20): a statement variable needs
no `let`, in a proof it stays the same statement, and an `assume` holds it
fixed in its block (§5.1). You'll see `$`-variables and `%`-variables throughout every
`.kurt` theory file under `src/kurt/theories/`.

### 3.3 What "new" means

Because there's no separate declaration step for most symbols, `const`/
`var`/`prop` mostly exist to be explicit, to catch typos (redeclaring the
same symbol raises an error), and to control what "new" means for keywords
that require a genuinely fresh symbol (`def`, `let`, `pick`, `brackets`).

### 3.4 Who declares what: the rules in one place

Most symbols are declared by using them. What each kind of line does to a symbol:

| line | the symbol is then |
|---|---|
| `$x`, `%A` anywhere | a variable, by its name alone: `$x` for a term, `%A` for a formula (never declared, never a constant) |
| `var x` | a variable (also an operator: `infix ∘ 50 50` and then `var ∘`) |
| `const x` | a constant |
| `brackets ⟨ ⟩` | both brackets constants |
| `def g = ...` | `g` a new constant (a new symbol on the right side is introduced as on any line) |
| `let x`, `pick x` | a constant inside the block (one arbitrary object); after the block, `x` is free again |
| `assume P $x` | `$x` fixed inside the block (not a variable there) |
| `arity`, `infix`, `prefix`, `postfix`, `prop`, and a declared sort such as `nat` | declared, but neither constant nor variable: these give shape or type information only |
| `sort nat` | `nat` a reserved sort name and declaration keyword, never a term symbol |
| `bindop`, `flat`, `sym` | a constant: each gives the named operator fixed semantic behavior |
| `chain OP...` | every named relation a constant with boolean result (`prop OP 0`), because `chain` adds fixed transitivity rules |
| `builtin x operation` | `x` a constant with the fixed calculator meaning (a bracket binding applies to the bracket expression); with a role of the engine (`builtin iff equivalence`), `x` keeps what it is |
| `alias new old` | `new` another spelling of `old`, including `old`'s constant/variable role and properties |
| the first use in a formula of a symbol that isn't a variable | a constant, reported as `const SYMBOL ; added constant` |

Further rules:
- **The prop signature comes from the first use** (§5), unless declared with `prop`: a symbol
  at a boolean position is boolean (`use P a` makes `P` boolean, `a` not), an operator whose
  arguments are boolean gets these positions. Each inferred signature is reported as a valid
  declaration, for example `prop P 0 ; added statement places`.
- **Declare before the first use.** After it, `const`, `var`, `prop`, a user sort, `arity`, `infix`,
  `prefix`, `postfix` for that symbol are errors ("already used in a formula"): the formula was
  read with what was known then.
- **Syntax and meaning are separate.** Fixity, arity, `prop`, and optional sorts say how a symbol is parsed and
  typed; they deliberately do not decide whether it is a constant or a variable. `bindop`,
  `flat`, `sym`, `chain` and calculator bindings do decide: their behavior belongs to one fixed
  operator, so Kurt makes it a constant and prints the implied declaration. A variable operator
  may still have fixity, arity and a prop signature, as `group.kurt`'s schematic `∘` does.
- **The variable of a binder.** Without a condition, `∀ x (...)` binds `x` (a new name or a
  variable; it doesn't become a constant). With a condition, it binds the first symbol of the
  condition, as written, that is new or a variable and not bound by an enclosing binder:
  `x` in `∀ x > 0 (...)`, `x` in `∀ c < x (...)` with a constant `c`, `$x` in `∀ (P $x) (...)`
  with a predicate `P`, `x` in `∀ (0 < e) (∀ (e < x) ...)`. Kurt decides it when it reads the
  line and stores it with the condition (§4.4), so the binder binds the same variable for the
  rest of the file -- also when a block closes and its constants are free again. A condition
  without such a symbol is an error ("has no variable to bind").
- **`load`** brings the symbols that the exported facts need and the ones the file declares at
  its top level without `local` (§8.2), with their declarations.
- **`--strict`** (§1) keeps all these rules but one: the first use of a symbol that wasn't
  declared at all (neither by a line of the table nor by an earlier use) is an error, not a new
  constant. A declaration like `prop Q` or `infix ∘ 50 50` counts. (It also refuses `use`,
  `todo` and `chain` outside the trusted theories.)

`tutorial/20-constants-variables-and-declarations.kurt` shows these rules, one at a time.

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
and associativity: for `infix`, `lbp > rbp` makes the operator *right*-
associative (as `implies` is: `infix implies 13 12`, so `A implies B
implies C` parses as `A implies (B implies C)`; and numbers.kurt's `infix ^
75 74`, so `2 ^ 3 ^ 2` is `2 ^ 9`); `lbp == rbp` (as with `+` above) makes
it left-associative (`a - b - c` is `(a - b) - c`), and a `flat` operator
(§4.5) collects all its arguments anyway. Declaring the same symbol both `infix` and `prefix` is
allowed (useful for something like unary/binary `-`); declaring it as more
than one of `infix`/`prefix`/`postfix`/a bracket otherwise is an error.
Fixity alone does not classify a symbol as constant or variable.

Called with no arguments (`infix`, `prefix`, `postfix`), each prints every
currently-declared operator of that kind, across all open levels. The other
property keywords (`const`, `var`, `sort`, `prop`, `arity`, `brackets`, `bindop`,
`chain`, `flat`, `sym`, and `alias`) work the same way. Every listed entry's
comment gives both its scope level and the source location that established
that exact property, for example `; level 1, natural.kurt:20`. A basename is
shown normally; if two loaded files have the same basename, Kurt shows their
paths to keep the locations unambiguous. Hard-coded core declarations have no
source line and therefore show only their level.

### 4.2 `brackets`

    brackets LEFT RIGHT     ; e.g. brackets "[" "]"

Declares a new matching pair of bracket symbols. **Only Kurt's own `(` `)`
pair (declared exactly this way in `minimal.kurt`) is treated as pure,
disappearing grouping** — `(A)` really is just `A`. Any *other* bracket
pair you declare yourself stays around as a genuine operator: `[A]` parses
to a real term whose operator is an internal name combining `[` and `]`
(rendered as `[]` if you `parse`/`format sexpr` it), not to `A`. Custom brackets
are meant to carry their own meaning (e.g. `⟨a, b⟩` for a scalar product,
`brackets ⟨ ⟩`; in the shell `\langle`, `\rangle`) via `arity`/`prop`/`use`
axioms about the resulting operator, not as alternative parentheses. `brackets` takes exactly the two
symbols — there is no separate binding-power argument.
The two delimiter symbols become constants. A later `prop LEFT ...` or `builtin LEFT ...`
declaration applies to the combined bracket expression, and listings print the source left
delimiter rather than its internal combined name.

### 4.3 `arity`

    arity SYMBOL N         ; e.g. arity f 2:         f a b
    arity SYMBOL SHAPE     ; e.g. arity g (_, _):    g(a, b), one argument, a pair
                           ;      arity sum _ (_, _) _:  sum i (0, n) f

Declares that `SYMBOL` is a plain (non-infix/prefix/postfix) function or
predicate symbol taking exactly `N` arguments by space-application: `f a b`
parses as one call `(f a b)`. The shape says more, written as the symbol is
used: `_` for an argument, `(_, _)` for a tuple of two (also nested, `((_, _),
_)`); Kurt checks each use, so `g(a)` or `g(a, b, c)` with `arity g (_, _)` is
an error ("`g` takes `g (_, _)`"), and a variable may stand for a tuple
(`g($p)`). A symbol with no declared arity defaults to arity 0: it takes all
the arguments that follow it, curried, and nothing checks them (§3.1). You
cannot set an `arity` on a symbol that's already `infix`/`prefix`/`postfix`
or a bracket (their arities — 2, 1, 1 — are implicit and fixed), and you
cannot re-set an arity once declared.

Round brackets group, so `f(x)` is `f x`, `((a))` is `a`, and `f(x) = x * x`
reads as usual. Round brackets around a list are a tuple, a term of its own
(since 0.9): `(a, b)` is a pair, `(a, b, c)` a triple, and `(a, (b, c))` a pair
whose second component is a pair -- so `g(a, b)` is `g` applied to one
argument, the pair, never `g a b` (before 0.9: `g a b` for a `g` of arity 2).
`a, b, c` without round brackets is a list: the elements in `{a, b}` or
`⟨a, b⟩`, or the formulas of `use A, B`; `{(a, b)}` is the set with one
element, the pair. Binders (`sum`, `∀`, ...) take their arguments as written,
e.g. `sum i (0, n) f` with the pair `(0, n)`.

`def` defines a function of a tuple by its components, `def f($x, $y) = ...`:
tuples are free, two are equal only if their components are, so this is
conservative (doc/kurt-soundness.md §8.14).

An operator alone in round brackets is the operator itself -- as the argument of
an operator parameter, `group(G, (∘), e, inv)`, `group(R, (+), 0, (-))`; `(- x)`
is still `- x`. An operator is no object (§5.3): elsewhere, `(+)` or a bare `f`
is a type error. An operator can also be a variable -- `var ∘` and
`infix ∘ 70 70` -- then `$a ∘ $b` in a rule matches `x + y` as well as `a ∘ b`
(by the rules of the operator it stands for, e.g. `flat`, `sym`). See
`group.kurt`.

A relation as a parameter works the same way: a variable with a boolean result,
`var R` and `prop R 0`, then `R(x, y)` -- or with `infix R 20 20` also `x R y`,
which matches `x < y` or `x ∈ y` -- e.g. `def reflexive((R), $A) ⇔ ∀ x ∈ $A (x
R x)`, and then `reflexive((<=), A)`. (`$R(x, y)` is a term, not a formula: a
`$` variable stands for a term.) The symbols `~`, `∼` (`\sim`), `≈`
(`\approx`), `≺` (`\prec`), `≼` (`\preceq`) are free for relations of your own.
Names may end in primes, `a'`, `f''`, and a Greek letter may have digits, `λ1`.

Empty brackets (`()`, `{}`, ...) are allowed and parse to nothing; the only
place this is meaningful is directly after an arity-0 symbol, where `f()`
then parses to *exactly* `f` — the same expression as writing `f` alone,
matching ordinary mathematical usage of `()` for "no arguments." Directly
after a symbol with a declared arity of 1 or more, `f()` is instead a
clear, specific `EvalError` ("empty brackets `()` cannot supply an
argument for `f`, which needs N argument(s)"), not a confusing parse —
empty parens can never actually supply a real argument.

### 4.4 `bindop`

    bindop SYMBOL     ; e.g. bindop forall

Declares `SYMBOL` a *variable-binding operator*: its first argument is
treated as a bound variable (or, with the sugar below, a boolean condition
whose free variable is the one being bound) for the rest of the
expression. `forall`/`exists` are declared exactly this way, in
`logic.kurt` (`arity forall 2, exists 2`, `bindop forall, exists`), together
with their roles (`builtin forall universal, ...`, §8.1) and their axioms
(`forall-elim`, `exists-intro`).
For a plain space-applied binder, the symbol must already have an `arity` of at least 2 (the
bound variable plus at least one more argument). An infix operator may instead be a binder, as
set-builder `|` is: its left operand contains the condition and its right operand is the body.
A binder cannot also be prefix, `flat`, `sym`, chained, calculator-bound, variable, or already
used in a formula. `bindop` gives a fixed scope rule, so it makes the symbol a constant and
reports `const SYMBOL ; added constant` when that role was not already explicit.

The scope of the bound variable is the condition and the *last* argument,
the body; arguments in between are outside of it, as in mathematics: in
`sum i (a, b) T` the range `(a, b)`, in `lim v a T` the point `a`. So in
`sum x (0, n) (sum x (0, x) x)`, the inner range `(0, x)` is the outer `x`.

A schema variable in the body of a binder normally stands for something
that does *not* depend on the bound variable — in `(∀ $x ($x = $T))`, `$T`
is one fixed term. A boolean `%A` may depend on it (that's what
"forall-elim" is about), and so may a non-boolean `$T` of an axiom that
occurs as the *whole* body of a binder over the same variable, and
otherwise only inside binders over it or as the body of a `sub` for it, as
in the sum axioms `(sum $i ($a, $a) $T) = sub $i $a $T` and
`(sum $i ($a, $b+1) $T) = (sub $i ($b+1) $T) + (sum $i ($a, $b) $T)` (see
`analysis.kurt`) — such a `$T` stands for any summand, which the axioms
only ever use for the bound `$i` or with something substituted for it —
or in the sum rule of derivatives, `(diff $v $a $S) ∧ (diff $v $a $T) ⇒
(deriv $v $a ($S + $T)) = ...` (`derivative.kurt`). Only an axiom (`use`,
`def`, `todo`) is read like this, and not the variables of the `∀`s it
writes out: a proven fact holds for every *term* in place of its
variables (a proof with `let c` is about terms `c`). This is decided by
the form of the rule alone: there is no way to declare a dependence
(`$T[$i]`, as in Isabelle) or a distinct-variable condition ("`$x` doesn't
occur in `$T`", as in Metamath) -- a decision (2026-10-06): the form shows
where a dependence is meant, the kernel checks it, and no theory has needed
more. Anywhere else, `$T` can't depend on the bound variable, and a rule
that would need it can't be written.

**Conditions.** The "bound variable" position may instead be a condition on
it: `∀ $n ∈ Nat P($n)`, `∃ $d > 0 ...`, `lim $x > 0 0 (f $x)`. Unbracketed,
it is a relation whose left-hand side is the variable; its right-hand side
extends over infix operators (`∀ $x ∈ A ∪ B ...`) but stops at the first
function application, which is where the body starts -- except for `f(x)`
written without a space, which stays in the condition (`∀ $x ∈ Perp(M) ...`).
In parentheses, any condition works, `∀ ($x > 0 ∧ $x < 1) (P $x)`. **Which
variable is bound:** the first symbol of the condition, in the order it is
written, that is new or a variable and not bound by an enclosing binder --
constants, predicates and operators are skipped. So `∀ x ∈ M ...` binds a
new `x` (also a plain name outside of a block), `∀ ($a ∈ $G) ...` in a rule
binds `$a`, `∀ ($x < $y) ...` binds `$x`, `∀ c < x ...` with a constant `c`
binds `x`, `∀ (P $x) ...` with a predicate `P` binds `$x`, and in
`∀ (0 < e) (∀ (e < x) ...)` the inner binder binds `x` (`e` is bound
outside). Kurt decides this when it reads the line, before anything is
reordered (a `sym` operator sorts its arguments), and stores the variable
with the condition: the binder binds the same variable whenever the formula
is used later, whatever is a constant then (when a block closes, its
constants are free again -- this used to change the reading, and Kurt
refused such a block). A printed formula reads back the same way. A
condition without such a symbol is an error ("has no variable to bind").

A condition is part of the formula: `∀ $x > 0 P($x)` is not the same
formula as `∀ $x ($x > 0 ⇒ P($x))`, and the engine doesn't treat it as an
implication. What a condition means is said by rules, like for any other
operator — for `∀` and `∃` in `logic.kurt`:

    use (∀ (sub $x $v %C) %P) ∧ (sub $x $a %C)  ⇒  sub $v $a %P                     "forall-cond-elim"
    use (sub $x $a %C) ∧ (sub $v $a %P)  ⇒  ∃ (sub $x $v %C) %P                     "exists-cond-intro"
    use (∀ (sub $x $v %C) %P)  ⇔  ∀ $w ((sub $x $w %C) ⇒ (sub $v $w %P))           "forall-cond-def"
    use (∃ (sub $x $v %C) %P)  ⇔  ∃ $w ((sub $x $w %C) ∧ (sub $v $w %P))           "exists-cond-def"

In a rule (`use`/`def`), a binder `sub $x $v %C` stands for *any*
condition: `$v` is the bound variable, and `%C` the condition with the
hole `$x` for it — matching `∀ ($y > 0) ...` gives `%C = $x > 0`, with
every occurrence of the bound variable in the hole. So `%C` never mentions
the bound variable itself, and `%C` may only be used with something
substituted for `$x`, as `sub $x ... %C` (checked when the rule is
stated). A binder with a condition never matches one without, so rules
for both kinds are written separately (see `lim` in `analysis.kurt`).

So from `∀ $x > 0 P($x)` and `1 > 0` follows `P 1` in one step
("forall-cond-elim"), while `∀ $x ($x > 0 ⇒ P($x))` takes a step of its
own ("forall-cond-def") — e.g. to close `∀ $c ($c ∈ A ⇒ $c ∈ B)` (the
definition of `A ⊂ B`) after a `let x ∈ A` block, which gives
`∀ x ∈ A (x ∈ B)`.

**Unique existence.** `logic.kurt` declares the binder `existsunique`, written
`∃! x P(x)` (`∃!` is one symbol; in the shell `\exists!`). Its meaning is its
definition, "existsunique-def": `∃! x P(x)` iff `∃ x (P(x) ∧ ∀ y (P(y) ⇒ y =
x))`; with a condition, `∃! x ∈ M P(x)` is `∃! x (x ∈ M ∧ P(x))`
("existsunique-cond-def"). Three rules follow from the definition and save
the steps through it: "existsunique-intro" (from `P(a)` and `∀ y (P(y) ⇒ y =
a)`), "existsunique-exists" (`∃!` gives `∃`), and "existsunique-unique"
(from `∃! x P(x)`, `P(a)` and `P(b)` follows `a = b`). They are axioms, since a
general proof would need `sub` in its lines; proofs/natural-deduction/
existsunique.kurt derives each of them from the definition alone, for a
predicate `P`. To use the witness, get `∃ x P(x)` and `pick` from it, or
unfold the definition.

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
operator already has a partial `prop` signature (§5), that signature must
be consistent with binary use (both argument positions boolean, or
neither; no signature information beyond position 2).

Declaring `flat` or `sym` is a claim (associativity, commutativity), so it
must come before the operator is used in any formula, and it can't be made
for an operator that comes with one of Kurt's theories or its core (e.g.
`sym -` or `sym implies` is an error) — see "frozen operators" in §8.2.
It also fixes the operator's meaning, so either declaration makes it a constant. A `flat`
operator cannot share its symbol with a prefix form (flattening would erase the distinction
between unary and binary trees); neither property can be attached to a binding or variable
operator.

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
$b < $c implies $a < $c`, but also every *mixed* pair like
`$a <= $b and $b < $c implies $a < $c`. They are named "chain-trans-I-J", by the
positions of the two relations in the chain (counted from 0): `<` with `<` is
"chain-trans-2-2", `=` with `<` is "chain-trans-0-2". So given `x = y` and `y < z` as
two separately-proven facts (not written as one continuation-line chain),
`x < z` really is now a single derivation step, citing the
auto-generated fact — you don't need to hand-write these per theory
(`numbers.kurt` used to; it no longer does). This only combines *two*
facts in one hop, the same as every other inference rule — three or more
links in a chain of relations still need an explicit intermediate step,
same as any other multi-hop reasoning (§6.1's single-hop limitation still
applies beyond one combination).

Relations can also be chained on a single line: `a = b <= c < d` means `a =
b and b <= c and c < d`, reusing each middle term. This applies to any infix
operator with a boolean result and no boolean arguments (`prop OP 0`, e.g.
`=`, `≠`, `<`, `<=`, `in`), whether or not it is declared in a `chain` —
not to connectives like `and`, `iff`, `implies`. The operators of one chain
must have the same binding power: with `infix <= 50 50, < 50 50` and `=` at
`20 20`, `a = b <= c < d` is not a chain but `a = ((c < d) and (b <= c))`.
Parentheses switch it off:
`(a = b) = c` is still an equation between `a = b` and `c`. Since the
auto-generated transitivity axioms take a conjunction as premise, a chain of
two relations on one line like `a = b <= c` directly gives `a <= c` in one more step
(`proofs/arithmetic/chains.kurt`); with three, `a = b <= c < d`, `a <= c`
is not derivable in one step. A same-line chain can't (yet) be
continued on indented lines below it.

Continuation lines must be indented relative to the line that starts the
chain; writing the continuation at the same indentation is a `ParseError`,
not a chain. All declared chains together must form a DAG (no operator
ordering may create a cycle across different `chain` declarations) — this
is checked when the chain is declared.
Every member must be a constant, non-binding infix relation with boolean output. `chain` adds
those `const` and `prop OP 0` declarations when necessary and reports them explicitly; a
variable operator cannot acquire the generated fixed transitivity rules.

A chain has at most three operators (at most 9 rules). With `--strict` (§1), outside the
trusted theories, a `chain` generates nothing: each of its rules -- one for every ordered pair,
`($a Ri $b) and ($b Rj $c) implies ($a Rk $c)`, the later relation absorbing the earlier, so
`chain = <` is a different claim than `chain < =` -- must be a fact before the `chain` line, or
follow in one step (checked as a line is: the search, then the kernel); a missing one is an
error that lists the `show` lines to prove. The chain's notation (continuation lines, `a ≺ b ≺
c`) then uses the proved facts. Unproven, `chain R` for `x R y` meaning `y = x + 1` would give
`3 = 2`.

### 4.7 `alias`

    alias NEW OLD     ; e.g. alias "⇒" implies

`alias` gives an existing symbol an additional name, resolved *in the
scanner* (i.e. before parsing, with no inference step) — `implies` and `⇒`
are completely interchangeable everywhere, including inside axioms already
stored in the theory. This is different from `def` (§6.2), which
introduces a genuinely new constant that needs an inference step to
unfold (`equal-elim` for `def c = ...`; a `def P iff ...` is used directly as
an implication in both directions).

### 4.8 Inspecting the grammar

`syntax` (with no argument) prints every declared piece of syntax at every
open level; `syntax SYMBOL` prints just what's known about one symbol. For
the facts that mention a symbol too, not just its declarations, see `info`
(§4.9).
`parse EXPR` parses `EXPR` without checking it and prints both its
s-expression form -- in the normal form Kurt stores and matches (`flat`
operators flattened, the arguments of `sym` ones sorted: `parse c + 1 + c`
gives `(+ 1 c c)`) -- and the same per-symbol syntax info as `syntax`.
`tokenize EXPR` shows the raw token stream before parsing. Each of
`infix`/`prefix`/`postfix`/`brackets`/`arity`/`bindop`/`flat`/`sym`/
`chain`/`sort`/`prop`/`var`/`const`/`alias`, called with no
arguments, also prints its own currently-declared table.

### 4.9 Inspecting loaded theories

`list` shows which theory files are loaded. `list files` is the explicit spelling of the same
command. Give it a loaded theory's stem or filename to see all declarations and formulas retained
from that source:

    list
    list files
    list natural
    list natural.kurt

A category before the optional source narrows the result:

    list const                 ; every known constant
    list const natural         ; constants originating in natural.kurt
    list infix natural.kurt    ; infix declarations originating there
    list theory natural        ; all retained formulas originating there
    list use natural           ; retained axioms originating there
    list def natural           ; retained definitions originating there
    list syntax natural        ; every retained declaration originating there

The declaration categories are `prefix`, `infix`, `postfix`, `brackets`, `arity`, `bindop`,
`flat`, `sym`, `sort`, `prop`, `chain`, `var`, `const`, and `alias`. A declared sort name is also
a category, so `list term lambda` shows the retained `term` signatures. After `list`, `symbols` and
`declarations` are synonyms for `syntax` (`list symbols natural`). Locations in a source-filtered result refer to the original file and line.

A source without `.kurt` matches the stem of a loaded file; a name ending in `.kurt` matches its
basename; and a path selects that file. If two loaded files have the same stem or basename, Kurt
asks for a path. Category names are reserved after `list`, so a theory called `const.kurt` is
selected with `list const.kurt`.

Loading retains a theory's exported declarations and labelled, non-`local` facts. Therefore
`list natural` describes the part of `natural.kurt` present in the current knowledge base, rather
than reproducing the source file. It cannot show local declarations, unlabelled facts, comments,
or intermediate proof lines that were discarded during loading.

`list`'s SOURCE is always a *file*. To ask about one *symbol* instead -- its declarations
(`syntax SYMBOL`), its `def` if it has one, and every retained fact that mentions it, wherever it
came from -- use `info SYMBOL`:

    load numbers
    calc on
    def four = 2 + 2
    four = 4
    info four
    ; const four                                ; ...
    ; def four = (2 + 2)                        ; ...
    ; four = 4                                  ; ...

`info` never resolves its argument as a file (unlike `list`), so a symbol and a loaded file
happening to share a name never conflict: `info four` always means the symbol, even with a loaded
`four.kurt` in scope -- `list four` still means that file.

## 5. Statements, terms and sorts

### 5.1 Statements and terms: `prop`

Kurt has two categories of expressions: **statements**, what is proved, assumed and combined with
`∧ ∨ ¬ ⇒ ⇔ ∀ ∃`, and **terms**, the objects -- `any` and the sorts below it (§5.2), which form a DAG
(`field ⊂ ring` and `field ⊂ ordered` is fine; where two sorts meet, the meet must be one sort).
`prop` declares which places take statements:

    prop P, Q              ; P and Q are statements (propositional constants)
    prop even 0            ; `even n` is a statement: the result place 0
    prop ∧ 0 1 2           ; `∧` takes two statements and is one
    prop = 0               ; `a = b` is a statement; its places 1 and 2 are terms

Position `0` is the result, `1`, `2`, ... the arguments; `prop P` is short for `prop P 0`. Every
place is a statement place or a term place: **a place `prop` doesn't name is a term place.**

**A statement is no object** (decided 2026-10-20): a statement at a term place is a type error --
`c = (A ∧ B)`, `A ∈ M`, `f(A ∨ B)` -- and so is a term at a statement place. Statements are compared
with `⇔`, not `=`. This is what the search and the kernel always did (no step puts a statement in
for a term variable), and what the Lean export says (statements are `Prop`, terms `Obj`).
Truth values as objects (a function into {true, false}, a Boolean algebra) are terms of a sort of
their own (`sort truth`), never statements.

**`prop` is no sort**: `sort prop` and `sort any prop` are refused, `sort` doesn't list it, no term
fits a statement place.

**Statement variables.** `%A` is a statement variable, by its sigil -- as `$x` is a term variable:
in propositional logic, the propositional variable; in a rule of first-order logic it may contain
the rule's term variables (`∀ $x %A` with `sub $x $t %A`). `var p` with `prop p` is the same with a
plain name (§3.2). A statement variable is **schematic**: free in a `use` or a `show`, it says "for
every statement" -- `use false implies %A`, `show %A ∨ ¬%A` -- and the search puts any statement in
for it. **Binders range over terms** (decided 2026-10-20): `∀ p (p ∨ ¬p)` with a statement `p`, and
`∀ %A ...`, are type errors -- nothing is lost, the schema says the same, and no file needed a
statement bound inside a formula (proofs/soundness/binders-range-over-terms.kurt). So `let`, the
introduction of `∀`, fixes a term only: a proof about `%A` needs no `let` -- the claim's `%A` is one
statement throughout the proof, an `assume` holds it fixed (proofs/soundness/let-fixes-a-term.kurt).

**First use.** A new operator applied to statements gets those places at its first use, and that is
final, like the first sorted use of §5.2 (`infix xor 20 20`, then `A xor B`: `xor` takes two
statements, `c xor d` with terms is then a type error); a new constant used as a statement becomes
one. Kurt prints the declaration it inferred, for example `prop P 0 ; added statement places`,
next to `const P ; added constant`. Use explicit `prop` declarations where stable vocabulary and
early typo detection matter; `--strict` additionally rejects undeclared symbols.

Only `use`/`show`/bare top-level claims are required to be statements overall (the error is "must
evaluate to boolean"); a binder's body is what the binder says -- a statement for `∀`, `∃` and
`{x ∈ A | F}`, a term for `sum`.

### 5.2 Optional user sorts

General sorts are optional. A theory that declares none has only the two categories of §5.1,
statements and terms (all of sort `any`).

Declare any additional categories a theory needs:

    sort nat, vec
    nat a, b
    vec v, w

Each new sort name becomes a declaration keyword with the same positional notation as `prop`:

    nat + 0 1 2            ; result and both arguments are natural numbers
    prop < 0               ; the result is a Boolean judgment
    nat < 1 2              ; both arguments are natural numbers
    vec · 0 2              ; vector result and second argument
    nat · 1                ; natural-number first argument

A convention of the theories, not a rule of the language: **sorts are lowercase, sets are
capitalized.** `real x` says what kind of thing `x` is (a sort, syntax); `x ∈ Real` is a fact about
`x` (a set, an object a fact can be about). The number sort is `real` (objects.kurt, `real ⊂ set`;
Kurt computes exactly with the rationals among them), the sets of numbers are `Nat`, `Int`, `Rat`,
`Real` (`ℕ`, `ℤ`, `ℚ`, `ℝ`).

Position `0` is the result; positions `1`, `2`, ... are arguments. A symbol without positions is
short for result position 0, so `nat a` means `nat a 0`. Unmentioned positions remain
unconstrained. Different sorts may describe different positions of one operator, but one position
cannot have two sorts. A sorted variable remains constrained when Kurt instantiates it as part of
a rule, including after the rule crosses a `load`; proof search and the certificate kernel both
check the constraint.

#### Subsorts

An item of a `sort` line is one name, or a chain of names read like `chain` (§4.6): `sort set real
int` declares the names that are new and makes `int ⊂ real ⊂ set`; commas separate items, `sort set
real, set vec` gives `set` two subsorts. The relation is a DAG with its transitive closure (`int ⊂
set` too); a cycle is an error, also one that a `load` would make. The line says what it
declared:

    sort set real int                          ; real ⊂ set, int ⊂ real

A value of a sort fits a position or a variable of the same sort or of a bigger one: a number
fits where a set is required (`3 ∈ {3}`), a set doesn't fit where a number is (`{1, 2} + 0` is a
type error). A sorted rule stays strict: a rule about the numbers never applies to a set, and one
about the sets applies to a number. A sort name where a symbol is declared is refused with a hint
(`set real` -- "a subsort is declared with `sort set real`"). `sort` alone lists the sorts and the
subsorts with where they were declared.

`any` is the sort of all objects, every sort is below it, and every symbol without a sort is over
all objects: a variable, a bound variable and a block's constant, inside a formula as at its top
(`∀ x (x ∈ A ⇔ x ∈ B)` is about all objects wherever it is written, so it meets "extensionality"),
and a constant until a use gives it a sort. `set` and `real` (objects.kurt) are restrictions below `any`, `real ⊂ set`: a binder over the
sets is one over fewer objects, like one over the numbers. set.kurt declares the places that are
sets (`set ∈ 2`, `set ⊂ 1 2`, `set ∪ 0 1 2`, ...) and has no `default`: an element (the left of
`∈`, an element of `{a, b}`, the variable of a set-builder, a component of a pair) is any object.

A fact gives no sort: `x ∈ Nat` says nothing about the sort of `x` (sorts are syntax, facts are
semantics). `∀ x ∈ Nat` ranges over the numbers where `x` is a number by its places (`x + 1`) or by
`default real`; natural.kurt's induction applies to it only then, so a proof about numbers
writes `default real`. There, `∀ n (n ∈ A ⇔ n ∈ B)` is about the numbers only and doesn't meet
"extensionality"; for sets of numbers natural.kurt has "ext-real": `(∀ n (n ∈ A ⇔ n ∈ B)) ∧ A ⊂ Real ∧
B ⊂ Real ⇒ A = B`, with the set `Real` of all numbers ("real-all": every number is in it) and `Nat ⊂
Real`, `Int ⊂ Real`, `Rat ⊂ Real` -- rules with proofs in Lean, not a link between sorts and sets
(proofs/natural-numbers/sets-of-numbers-are-equal.kurt). `ℕ`, `ℤ`, `ℚ`, `ℝ` (typed `\N`, `\Z`, `\Q`,
`\R`) are aliases of `Nat`, `Int`, `Rat`, `Real`. The elements of a set written by its elements (`{1, 2}`, `{0, 2, ...}`) have
the sort of the elements. A polymorphic rule writes its bound variable `$$x` (logic.kurt: `∀ $$x %A
⇒ sub $$x $a %A`): it is used for a binder over any sort, and the checker verifies that `$$x`
occurs only in its binder, in `sub`s and as a side of `=`.

#### Inference and `default`

A symbol without a declared sort takes the sort of its first sorted use, in every file: with `real
+ 0 1 2`, `const x` and then `x + 0 = x` make `x` a number; `x ∈ A` makes `A` a set. The line that
gives a symbol its sort says so, like an inferred `prop` signature:

    7  x + 0 = x                     ; by add-identity
       real x                         ; sort inferred

`info x` shows the sort and how it came (`real x 0 ; level 1, f.kurt:7 (inferred)`), and so does the
hover of the line in an editor. `=` is polymorphic: it gives no sort.

Where a use also takes smaller sorts -- the left of `∈` takes any set, and a number fits -- the
`default` of the file decides, if it fits; without one, the position's own sort (`x ⊂ A`: a set).
The default decides only at an element (the left of `∈`, an element of `{a, b}`), not at a set:
in `$a ∈ $A`, `$A` stays a set. Before its first sorted use (`x = y`: `=` gives no sort) a symbol
has none: it is any object.

**The first sorted use is final.** No later line changes the sort of a symbol: `x ⊂ A` makes `x` a
set, and a later `x + 1` is a type error, also though a number is a set. To use it as a number,
declare it before its first use (`real x`); a number fits wherever a set is required. The message
says both places and what to declare:

    TypeError: `x` has the sort `set` (inferred at line 3), but here it is used as `real` -- the first
    sorted use decides; to make it a `real`, declare `real x` before that use

A fact gives no sort -- `b ∈ Nat` doesn't make `b` a number -- and the message says that too, when
such a fact is known. A declared sort, the sort of a defined symbol (`def c = R`: the sort of `R`),
the sort of a witness (`pick w with ...`: the sort of the existential's variable) and that of a
symbol of a loaded file are final as well.

`default SORT` (only after `sort SORT`; not `prop`; at the top of a file, not inside a block):
from this line on, every `$` variable, operator position, bound variable and new constant of this
file without a declared or inferred sort gets SORT -- an operator's positions at its first use
after the line, except a boolean one, and a binder's variable with the binder (`sum i (0, n) i`:
`i` a number). The last `default` counts, from its line on. It doesn't cross `load`, but the sorts
it gave to the file's symbols do, as sorts do. `default` alone names the one in force. `default any`
is the same as none: a symbol without a sort is any object anyway, and a constant gets its sort at
its first sorted use. numbers.kurt,
natural.kurt, integer.kurt, rational.kurt and the analysis theories have `default real`; set.kurt,
group.kurt, field.kurt and vectorspace.kurt have none (their symbols are over all objects). A student's file has none, unless it wants one: after `default real`, every
symbol that has no other sort is a number. "No other sort" includes what the line itself says: in
`use A = {n ∈ Nat | n > 2}` the other side of `=` is a set, so a new `A` is a set there, not a
number (`proofs/soundness/default-yields-to-equality.kurt`).

Variables (`$x`, a `var`, a bound variable) get their sorts per formula, from all their places in
it -- the same formula always reads the same; a constant of a block keeps the sort it got there
when the block closes: `let x`, then `x + 1 > x`, gives `∀ x (...)` over the numbers, also if the
last line doesn't mention arithmetic (the kernel checks it, doc/kurt-kernel.md).

#### A checker sort versus an object-level carrier

`sort nat` and `const Nat` express different design choices. A sort belongs to Kurt's checker:

    sort nat
    nat n

This constrains where `n` may occur, but `nat` is not a term, set, or proposition. In contrast,
`natural.kurt` declares `Nat` as an object-level constant (of sort `set`). Together with membership
from `set.kurt`, `$n ∈ Nat` is an ordinary mathematical proposition that can occur in assumptions
and theorems. The two don't meet: `n ∈ Nat` gives `n` no sort, and a checker declaration `real n`
does not prove `n ∈ Nat`.

A sort property does not decide whether a symbol is a constant or variable, just as `prop`,
`infix`, and `arity` do not. Write `var a` or `const a` when the role matters; otherwise the usual
first-use rule still applies. A declared sort name is reserved and cannot also be a term symbol or
Kurt keyword. Sort declarations and signatures must precede the symbol's first use.

For a binding operator, the declared sort of its first position also types a fresh bound name in
the body. `sub x a A` preserves the result sort of `A`; if `x` has a sort, its replacement `a` must
have it. A rule of logic.kurt, written with `$$x`, is used for a binder of any sort (`∀ x` over
the numbers): its bound variable stands for the binder's, and each `sub` checks the sort of what it
puts in -- all `$$` binders of one use over the same sort, and only a rule whose `$$` variable
occurs nowhere else but in `sub`s, `=` and where it is bound; "extensionality" (`$c` in its body)
is about all elements, and for the numbers alone it would make `∅ = {∅}` (doc/kurt-soundness.md
§8.41-§8.42).

#### Order-sorted logic, and why it is sound

These sorts make Kurt an order-sorted logic: a partial order of sorts with `any` on top, values
that fit wherever a bigger sort is required, and rules for every sort at once (`$$x`). What makes
that sound -- every variable has a sort, substitution respects it, binders are the same only over
the same sort, one sort per use of a polymorphic rule, `$$x` only where the sort doesn't matter,
non-empty sorts, a meet for every two uses of a symbol -- and where each is enforced (by the search
and again by the kernel) and tested (`proofs/soundness/`, Lean) is in doc/kurt-soundness.md §10.
Restriction (`∀ x:set P` to `∀ y:real P`) and widening (`∃ x:real P` to `∃ x:set P`) are no rules:
`let` with "forall-elim" and `pick` with "exists-intro" do them (proofs/restriction-and-widening.kurt).

Every top-level `sort` declaration crosses `load` as part of the theory's public vocabulary, even
if no exported fact uses it yet; so do the subsorts. Sort
signatures cross with the symbols that exported facts need (not those of `$` variables: their
sorts are in the facts), and all declarations retain their source locations. A sort is declared by
one file only (objects.kurt declares `set` and `real` for set.kurt and numbers.kurt, which both load
it). Inspect them with:

    sort                     ; prop plus every user sort, and the subsorts
    nat                      ; every nat signature
    list sort lambda         ; sorts retained from lambda.kurt
    list term lambda         ; term signatures retained from lambda.kurt

Generic equality deliberately remains polymorphic: `prop = 0` constrains its result but leaves its
two operands unsorted. A theory may add more specific operators when it wants stronger checking.

### 5.3 Operators are no objects; functions as values are mappings

An operator -- a function symbol (`arity f 1`), `+`, `∪`, a predicate -- is no object: it is
applied, never compared, quantified over, or passed where a term is required. `f = g` for two
function symbols, `P(f)`, a `∀ x` instantiated with `f`: each is a type error ("`f` is an operator
without its arguments -- an operator is no object; a function as a value is a mapping"). The one
exception is an *operator parameter*, a place where a defined predicate takes an operator: group.kurt
defines `group($G, (∘), $e, (ι))` with the operator variables `∘` and `ι`, so `group(R, (+), 0, (-))`
passes `+` and `-` there -- a schema, which the definition unfolds into first-order formulas about `+`
and `-`.

A function that is a value is a *mapping* of set.kurt: a set of pairs, `f ∈ A → B`, applied by
juxtaposition, `f a`. Mappings are objects: they are compared (two mappings from `A` that agree on
`A` are equal, "function-extensionality"), they are elements of sets, a quantifier ranges over them.
Like every fact, `f ∈ A → B` gives `f` no sort; declare `set f`
(proofs/set-theory/function-extensionality.kurt):

    set f, g
    use f ∈ (A → B)
    use g ∈ (A → B)
    use ∀ a ∈ A (f a = g a)
    f ∈ (A → B) ∧ g ∈ (A → B) ∧ ∀ a ∈ A (f a = g a)
    f = g                                 ; by "function-extensionality"

*Why* (decided 2026-10-20). Until then an operator was also a value: `f = g` was accepted and
rewrote `f c` to `g c`, `P(f)` was a formula, and `∀ k` included the operators. That has no
first-order meaning: the soundness argument (doc/kurt-kernel.md §8) models an operator as a total
function, not as an object, and in the model of the Lean export -- ZF sets -- `∪` or a field's `+`
as an object would be the graph of an operation on all sets, a proper class. A bare operator also had
the sort of its result, so with `real f 0 1` the function `f` counted as a number (`f + 0 = f` was
well-sorted, and a fact about all numbers applied to `f`). Making operators first-class objects
would have meant an applicative semantics, a sort of its own for operator values and a Lean model
with objects that are no sets -- higher-order logic through the back door. Kurt stays first-order:
operators are applied, mappings are the functions one can talk about, and the operator parameters of
structures are schemas. The search (`bare_operator_for`), the kernel (`k_has_kind`) and the type
check (`bare_operator_as_value`, `operator_parameters`) agree on it.

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
and then combined via "and-intro" (this, "impl-elim"/modus-ponens
against every formula currently in scope, and "top-intro" for the literal
symbol `true` are the primitive rules hard-coded in Python; the engine also
uses an `iff` fact as an implication in both directions, computes "by calc",
closes `case` blocks "by case-elim", and generates the "chain-trans-I-J" rules
of a `chain` -- see §8.1). Derivation is a *single* hop: given `A`, `A implies B`, and `B
implies C` all separately in the theory, deriving `C` in one step is *not*
automatic — you must first derive `B` as its own line.

When a claim fails, Kurt says that no one-step derivation was found and shows at most three
relevant rules whose conclusions match the goal, together with their missing premises. These are
bounded search diagnostics, not proof certificates and not a claim that the formula is false.
The structured form is available as `CheckResult.failure`, in the failing JSON event, and in the
LSP diagnostic's `data.failure` field.

Where the claim and every fact of the context are propositional, Kurt also looks for a
**counterexample** by truth table: an assignment of the atoms that makes every fact true and the
claim false. If there is one, the explanation ends with a line like

    a counterexample: with `A` false, `B` false and `C` true, every fact holds but the claim doesn't -- it does not follow from these facts

(here for the claim `B` from `A ⇒ B` and `A ∨ C`), and `failure.counterexample.assignment` has
the assignment, `{"A": false, "B": false, "C": true}`. Unlike the missing premises, this is a
statement about the claim itself: no proof of any length derives it from these facts. The
connectives with a truth table are `∧`, `∨`, `¬`, `⇒`, `⇔`, `true` and `false`; any other
statement (`A`, `P a`, `x ∈ B`) is an atom whose truth is free, so a fact with a quantifier or an
object variable (`$x`) -- every rule of logic.kurt, equality.kurt and the theories on them has
one -- or with a statement under an operator the table doesn't know (`A ⇐ B`) means the facts
can't be evaluated, and nothing is said, whatever the atoms: in practice, counterexamples come
in propositional contexts (the core, propositional.kurt, `prop A, B`). The rules of propositional.kurt, which are
schemas over statements (`%A ∧ %B ⇒ %A`), hold in every row. The table has at most 12 atoms and is given a fraction of a second; beyond
that, nothing is said either. When no counterexample is reported, nothing follows from that: the
claim may well hold, in more steps than one. The assignment is checked again, with an evaluator
separate from the one that searched for it, before it is reported; the check runs only after a
line has failed, so it never changes what Kurt accepts.

**Running time.** Since a claim is one step, its search is bounded: Kurt tries the facts, then the
rules whose conclusion can match the claim (found by an index on the top-level operator of the
conclusion), and for each rule the facts for its premises. What makes a line slow is
therefore not the length of a proof but how many rules could have concluded the claim, times the
size of the theory their premises are searched in: a theory with many rules for the same
conclusion (or rules whose conclusion is a mere schema, like "equal-elim") makes every line
that reaches them slower. The lessons and most proofs of this repository check in a second or
two, the larger theories (natural.kurt, field.kurt) in several seconds; `scripts/bench.py`
measures a set of representative files (before and after a change to the search;
dev/dev-notes.md, "speed", has the history). A `.kurtc` file (§1) makes a file that is checked
again much faster, since each step first tries its stored certificate.

One exception, for rewriting: a rewriting step (a chain `X = A` / `= B`, or a
claim that changes one place of a recent fact) may use a rule with
conditions, e.g. `$a ∈ K ⇒ 1 · $a = $a`, if the conditions are facts. Kurt
then derives the instance (`1 · b = b`, with the fact `b ∈ K`) as a step of
its own, shown as line `17a` before line 17, and rewrites with it. Both steps
have their certificates, which the kernel checks.

The first line of a chain, `L = R`, is rewritten like the later ones, as if
`L = L` (equal-intro) were the line before it: `a ∘ e = a ∘ (inv(a) ∘ a)`
follows by "left-inverse" inside the term. And a line that changes up to four
places at once, `x + y = 0 + 0` from `x = 0` and `y = 0`, is checked place by
place: Kurt adds the lines in between as steps of their own (`17a`, `17b`,
...), each one rewrite with its certificate. Both are tried only when nothing
else gives the line.

A rewrite may also change a *part* of the arguments of a `flat` operator, where
flattening removed the node: in `x·x + x + (- x) + (- 1)`, the rule `$c + (- $c) =
0` rewrites `x + (- x)` (for a `sym` operator any part, otherwise only arguments
next to each other: `b · l · a` to `b · a · l`). The place is found by comparing
the line with the one before; the kernel flattens after substituting, as always.

A claim that's structurally identical to the last thing already in the
theory is logged as a restatement of it (`by 2`), without being added again.
Each checked line is logged with the short form of its certificate (§6.5):
the rule, applied to the facts it was used with -- `by 13(14)` is the
(unlabelled) implication of line 13 applied to the fact of line 14,
`by equal-elim(11, 10)` the rule "equal-elim" applied to lines 11 and 10,
`by 3` an instance of the fact of line 3, `by and-intro(12a, 12b)` a
conjunction checked conjunct by conjunct. The result of a block that closes
is numbered by the lines of the block, from the line that opened it to its
last one, `; 15-23 by impl-intro` (the `assume` at line 15, the block to line
23; with `false` at its end also `; 15-23 by not-intro`), and a step that uses
it names them: `by case-elim(14, 15-23, 24-30)`. A cited line that is only
admitted (`todo`, §6.3) says so: `by and-intro(5, 6 (todo))`. In front of a line of the file,
Kurt prints its number, and the reason goes without it; a derived line has no number in front,
its number is in the reason (`; 12a by and-elim(12)`, `; 15-23 by impl-intro`) -- `kurt
--no-line-numbers` prints every number in the reason instead (`; 4 by 2(3)`). If the line has a
comment of its own, the comment stays on the line, and the reason goes on the next line:

       4  B                                         ; modus ponens
                                                    ; by 2(3)

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

### 6.2 How to define things: `def` and `use`

    use EXPR              ; use EXPR "label"
    use EXPR local "label"
    def SYMBOL = EXPR
    def SYMBOL iff EXPR

There are two ways to write what mathematicians call a definition, depending on what kind of
definition it is:

- Use `def` for a **conservative definitional extension**: one fresh name is introduced as an
  abbreviation for a term or property already expressible in the language.
- Use `use` for any broader defining principle, including a recursive, conditional, implicit, or
  characterizing definition. Such a statement is an **axiom** to Kurt, even when its label ends in
  `-def`.

For example, these only add names for expressions the language already has:

    def four = 2 + 2
    def square($x) = $x * $x
    def even($n) iff exists $k ($k in Nat and $n = 2 * $k)

Every accepted `def` is intended to be eliminable: expand the new symbol by its definition and the
theory says nothing new in its old vocabulary. Thus `def` expands the language without increasing
the mathematical strength of the theory. Kurt checks the syntactic conditions described below;
the soundness of that check is part of Kurt's trusted definition boundary.

A recursive definition is not such a simple abbreviation. Kurt currently has no termination,
constructor, or coverage checker with which to justify one as conservative, so write its equations
as explicit defining axioms:

    const fact
    use fact(0) = 1                                      "factorial-zero"
    use $n in Nat implies fact($n + 1) = ($n + 1) * fact($n)  "factorial-step"

The same applies when characterizing an existing object or notation, or when the defining equation
has conditions. `use` is the honest spelling: Kurt accepts the formula without proving existence,
uniqueness, termination, consistency, or conservativity. Such defining axioms can add genuine
mathematical strength and can make a theory inconsistent if they are wrong. Their necessary domain
conditions therefore belong in the formula.

`use` adds `EXPR` to the theory as an **axiom** — accepted without proof.
It is only allowed at the top level of a file, or inside a `sandbox` or
`expect` (whose content is discarded anyway) — not inside a `proof`,
`assume`, `case`, `let` or `pick`, where the result would look proven
although it relies on the axiom (e.g. `assume A` with `use B` inside would
give `A implies B` "by impl-intro"). State axioms before the proof, or use
`todo` (§6.3) for a step you want to leave open. The same holds for `def`,
`inline`, `chain`, and every grammar declaration (`infix`, `prefix`, `postfix`, `brackets`,
`arity`, `bindop`, `flat`, `sym`, `alias`, `sort`): not inside a `proof`, `assume`, `case`, `let`
or `pick` (`EvalError: \`def\` is not allowed inside \`assume\``), but in a `sandbox` or
`expect` -- declare them before the proof. For the grammar declarations this isn't only about
looking proven: a notation used by a formula that survives the block gets locked in for good
wherever that formula is visible, so it was never actually scoped to the block in the first place
(§11.2). An optional trailing string labels it. The label
is shown on the `use` output line and on later references and error messages instead of a bare
line number. When the axiom contains declared named variables, normal output also shows the
stored schematic form in a `; schema:` comment. For example:

    var x, y, ∘
    infix ∘ 70 70
    use x ∘ y = y ∘ x "comm"
    ; schema: $x $op $y = $y $op $x

Boolean variables use `%` names, term and function variables use `$` names, and a symbolic
operator variable gets a readable name such as `$op`. These generated names are stable display
names; they are not declarations and are not written into saved Kurt source. `format source`
continues to show the input line exactly, without the generated annotation. Formula listings
(`use` with no arguments, `theory`, and `list theory FILE`) repeat the annotation. The label also
controls whether
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

Operationally, `def` is `use` specialised to introducing exactly one **brand-new**
constant via an equation (`=`) or equivalence (`iff`) — the only two
top-level operators `def` accepts. Exactly one new symbol must appear on
the **left-hand side** (e.g. `def x = 18`, or `def $a ∩ $b = { $c ∈ $a | $c ∈
$b }` — infix notation puts the new operator between its arguments).
The left-hand side must be the new symbol itself or that symbol applied to
distinct variables, possibly curried. Defining a new symbol as an argument
of an existing operator is not supported: write `def injective($f) iff ...`,
not `def $f is injective iff ...`.

The new symbol must not occur on its own right-hand side, even through an
alias. It must not already have semantic declarations such as `calc`,
`flat`, `sym`, `chain`, or `bindop`. Comma-separated definitions are checked
left to right: `def p iff true, q iff p` is allowed, but defining the same
symbol twice, or defining a symbol already used by an earlier entry, is
not. A rejected batch adds no definitions or declarations.

On the right-hand side, a symbol that wasn't
declared is introduced as on any line (§3.4: a constant, reported as
`const g ; added constant`; an error with `--strict`): `def r = g b` with a new `g`
only names the term `g b`, whatever `g` is, so the definition stays
conservative. A declared operator isn't new even before its first use, e.g.
the comma of `def q = ⟨b, b⟩`. The right-hand side has no variables besides
those of the left-hand side. A definition is safe (it can't make the theory contradictory)
only if `=` and `iff` have their usual meaning, so `def` requires them to
come from the theories that come with Kurt: `load equality` (for `=`) or
`load propositional` (for `iff`) first — an `iff` or `=` declared some other way is
rejected. Once those checks pass, the defining equation is stored as a fact and can be used for
rewriting and inference like a `use` axiom. Its provenance remains `def`, because the reason it is
safe to admit is different: the checked extension is conservative rather than an additional
mathematical assumption. Both `use` and `def`, called with no
arguments, print everything `use`d/`def`ined so far.

**`inline`: a definition applied while reading.** A `def` is a fact, and
using it is a step: from `x > 0` to `0 < x` takes a line, and inside a formula
a rewrite. When two notations should simply be the same, `inline` defines the
new symbol by what it is read as:

    inline $a > $b   iff  $b < $a          ; numbers.kurt (also `>=`)
    inline $a ≠ $b   iff  not ($a = $b)    ; equality.kurt
    inline $A ⊃ $B   iff  $B ⊂ $A          ; set.kurt (also `∉`)
    inline sq $x     =    $x * $x          ; a term

Each use of the symbol is read as the right side, with the arguments for the
variables, so it is in no stored term: `x > 0` *is* `0 < x`, a rule written
with `<` applies to a line written with `>`, and nothing is to be switched.
Kurt prints the stored term (`0 < x`). The checks are those of `def`: the left
side is a new symbol (used nowhere yet; its syntax, `infix >`, may be declared
before), alone or applied to distinct variables; the right side has only these
variables, not the symbol itself, and no binder (an argument could be captured
by it -- use `def` there). `=` for a term, `iff` for a formula. A parameter may
also be a tuple of variables, `inline child($x, $y) iff parent($y, $x)` (an
argument must then be a tuple of that length). `inline` without arguments lists
the inline definitions; they are exported with `load`.

**Why not every `def` is an `inline`.** `inline` is for notation: the same
thing written differently -- a converse relation (`>`, `⊃`, `child`), a negation
(`≠`, `∉`), a short abbreviation of a term. A `def` gives a concept a name that
one reasons with: `subspace(U)`, `even n`, `group(G, ·)`, `orthogonal(x, y)`.
Inlined, such a name would disappear from every line and from Kurt's output
(which prints the stored term), the formulas would grow, the search would get
slower (more places where rules fit), and the step "by definition", which a
reader of a proof wants to see, would be gone. Most definitions also contain a
binder (`even n ⇔ ∃ k ...`), which `inline` refuses. So: `def` for what has a
name of its own in mathematics and theorems about it, `inline` for another way
to write the same thing (keywords/46-inline.kurt).

### 6.3 `todo`

    todo          ; admit the next step (a claim, or the goal at `qed`)
    todo EXPR      ; admit EXPR specifically, and add it to the theory

A joker: lets a proof continue (and the file still finish, with `Proof
almost checked: N todos.` instead of `Proof checked`, listing every
`todo`'s file and line) even though a step hasn't actually been justified.
Meant for iteratively developing a proof, or handing out a skeleton with
gaps left as exercises. A later step that uses an admitted line cites it as
`6 (todo)` -- also with `--all-errors`, where a line that fails is admitted
so that the check can go on.

#### 6.3.1 Definitions, axioms, admitted statements, and derived theorems

The way a formula enters the theory determines its status. Its label does not:

| Source form | Status | What Kurt checks |
|---|---|---|
| `def name = term` or `def predicate(...) iff formula` | conservative definitional extension | The syntactic conservativity conditions in §6.2. This extends the vocabulary without adding an assumption in the old vocabulary. |
| `use EXPR "label"` | axiom | `EXPR` is well formed and Boolean. Its mathematical truth and consistency are assumed. This includes recursive or other defining axioms. |
| `todo EXPR` or a step admitted by `todo` | admitted/incomplete | Enough syntax and bookkeeping to continue checking. The file remains visibly unfinished. |
| `show EXPR "label"` followed by `proof` ... `qed` | derived theorem | Every proof step and the final goal. `show` merely announces the planned claim; the theorem enters the theory when `qed` succeeds. |
| `EXPR "label"` as an ordinary line | derived theorem | Kurt derives the line from facts already available, and its certificate is checked by the kernel. |

For example, all four labels below are only names; they do not override the admission form:

    def square($x) = $x * $x              "square-def"       ; definition
    use fact(0) = 1                        "factorial-def"    ; axiom
    todo P                                 "future-theorem"   ; admitted/incomplete
    P implies P                            "identity"         ; derived theorem, if the line checks

In particular, `use ... "something-def"` remains an axiom, and a proved theorem does not become
an axiom because its label says `axiom`. A label controls how a fact is referenced and, together
with the absence of `local`, whether it is exported by `load` (§8.2). It does not change the fact's
provenance. This distinction is important when auditing a theory: a checked proof establishes its
conclusion relative to the `use` axioms, defining axioms, calculator semantics, and any `todo`s on
which it depends.

### 6.4 `theory`

    theory              ; print every formula, at every open level
    theory OP            ; print only formulas whose top-level operator is OP

Read-only introspection; changes nothing.

### 6.5 `cert`

    cert 17             ; the certificates of line 17 of this file (or of the shell)
    cert 17, 18
    cert 12-15          ; the result of the block of lines 12 to 15 (`; 12-15 by impl-intro`)
    cert                ; those of the last line with a step

The comment after a checked line, e.g. `by forall-cond-elim(8, 9)`, is a short form of the
line's *certificate*: what the kernel checks again, on its own, for each step (see
`doc/kurt-soundness.md` §9). `cert` shows it in long form: the rule and how it is read (as a
fact, or as premise ⇒ conclusion), the values of its variables, the fresh variables for `∀`s,
the facts that match the premise -- or, for closing a block, the block and its last line. The
kernel checks every step; should it ever reject one that the search found (a bug in Kurt), that
is a `KernelError`, which stops the file and can't be caught by `expect`. Variables are shown with the names they were written with (`$a`, `%A`, `x`), numbered where
several of them have the same name (`$x1`, `$x2`). A line that failed has no certificate; a line
that closes blocks by dedenting also has the certificates of the closings.

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
the block does not close: a `ProofError` at the `show` (where an editor
marks it), saying where the proof ends and what is missing -- ``the proof of
`A and C` (line 4) ends at line 7 without reaching its goal -- can not
derive `C` ``, whether `qed` or a dedent closed it.

`qed` is optional: dedenting alone already closes a `proof` block the same
way (§9 covers dedent-based closing in general). Writing `qed` additionally
checks that you really are closing a `proof` and not some other kind of
block, and documents where the proof ends; either way, `qed` must line up
with the indentation of the `proof`/`show` it's closing — dedenting is how
Kurt knows how many nested blocks to close, and a single `qed` can close
several at once this way. This is identical in a file and in the
interactive shell — see §9's introduction. The end of a file closes the
blocks still open like a dedent; a proof whose goal isn't reached there is a
`ProofError` at its `show`. A `qed` that isn't written is shown as a derived
line right after the last line of the proof (`qed ; 7a by or-intro(7)`;
in an editor, at that line).

## 8. Building the theory: hard-coded core vs. loaded theories

### 8.1 What's hard-coded (needs no `load`)

A pristine session starts with `minimal.kurt`'s worth of syntax (space,
comma -- `a, b, c` is one list, and `(a, b, c)` in round brackets a triple (§4.3) --, `(` `)`, `implies`, `and`, the constant `true`, the substitution
operator `sub` — `sub $x $a %A` is "`%A` with `$a` substituted for `$x`",
only allowed in `use`/`def` to write axiom schemas like "forall-elim" or
"equal-elim", and not nested (a rule about two variables is applied twice,
one variable at a time); where the search finds `$a` and `%A` for a given
formula, the hole `$x` is a subexpression -- a statement or a term --, and an
operator only if it yields a term: see "Where the hole of `sub` may be" below) already declared -- the quantifiers `forall`/`exists`
come with `load logic` (see below) --
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
- **an `iff` as an implication** — a fact `A iff B` (e.g. from `def P iff
  ...`) is used directly as `A implies B` and as `B implies A`, without a
  rule -- for the symbol with the role `equivalence` (propositional.kurt's `iff`, see
  `builtin`, §10).
- **"case-elim"** — closing the `case` blocks of a disjunction (§9.1) gives
  the goal; it is justified by propositional.kurt's "or-elim", for any number of
  alternatives.
- **"chain-trans-I-J"** — the transitivity rules a `chain` declaration
  generates (§4.6).
- **"by calc"** — with `calc on`, a claim that computes to `true`, or to a
  fact, follows by the built-in calculator (§10).
- **forall-elim, effectively for free** (with `load logic`) — every formula
  ever added to the theory has any *outer* universal quantifier stripped and
  its bound variable replaced by a fresh, freely-unifiable internal variable
  (as if it had been written as a `$`-schema to begin with) — so `use forall
  x (A x)` already lets `A a` derive for a specific `a`, with no explicit
  `forall-elim` step needed. The same for "forall-intro" (closing a `let`
  block) and "exists-elim" (closing a `pick` block). `logic.kurt`'s `forall-elim` axiom
  still exists for the same reason a hard-coded rule sometimes also has a
  `use` equivalent lying around: explicit intermediate steps, and cases
  this automatic stripping doesn't reach (a `forall` that isn't the
  outermost operator of a stored formula). Only a `forall` *without* a
  condition is stripped: `∀ $x > 0 P($x)` stays as it is, and is used via
  logic.kurt's rules for conditions (§4.4).

**Where the hole of `sub` may be.** A rule like "equal-elim", `($a = $b) ∧ (sub $x $a %A) ⇒
(sub $x $b %A)`, rewrites a formula by cutting a hole `$x` into it. The hole is a part of the
formula that is a term or a statement -- and an operator counts only when it is a term on its own.
A function symbol is: `f` with `arity f 1` is an object, which an equation can name. So `f = g`
rewrites `f a`:

    load equality
    const f, g, a
    arity f 1, g 1
    prop R
    arity R 1
    use f = g
    use R (f a)
    R (g a)                     ; by equal-elim(6, 7) -- the hole is the operator `f`

A boolean operator is not: `=`, `∧`, or a predicate `P` with `prop P` and `arity P 1` is, on its
own, neither a term nor a statement -- it becomes a statement only applied to its arguments. So
the hole is never the `=` of `c = c` (doc/kurt-soundness.md §8.40: cut there, "iff-subst" had
turned `R ((¬¬(=)) c c)` into `R (c = c)`), and a bare boolean operator where a statement is
required is a type error -- also an equivalence of two predicates:

    load propositional
    prop P, Q
    arity P 1, Q 1
    use P ⇔ Q                   ; TypeError: arg number 1 of `iff` must be a statement, but `P` is
                                ; an operator without its arguments -- apply it to its 1 argument, e.g. `P a`

State it for the arguments instead: `use ∀ x (P x ⇔ Q x)` (with `load logic`), and `P a` gives `Q a`.
A binder (`∀`, `∃`) is no hole either. An operator variable (`var ∘` with `infix ∘`) is a
different thing: it matches an operator by itself, through the unifier (`∘ := +`), not as a hole.

The quantifiers are declared in `logic.kurt`, which gives them their roles
(`builtin forall universal, exists existential`, §10): the engine strips,
closes `let` with, and opens `pick` from, only the binders with these roles.
So the core has no quantifiers: a file for propositional or modal logic
doesn't need them, a deep embedding may use the words for something else,
and without `load logic`, `let` (over terms) and `pick` say that they need it.

Notably, **"and-elim"** (splitting a proven `A and B` back into `A`) is
*not* hard-coded — you either state the specific instance yourself as a
`use` axiom, or `load propositional` for a general one. A general "restatement"
schema (`%A implies %A`) and a general "impl-intro" schema (`(%A implies
%B) implies (%A implies %B)`) are *also* not hard-coded, despite once
being drafted as if they were: a bare `A implies A` with nothing else
known does not derive from nothing. Prove a specific instance instead
(`show`/`proof`/`assume`/`qed`), or note that plain "restating" an
already-proven fact is covered anyway by "impl-elim"'s own premise-less-
implication case.

`minimal.kurt` is the core itself: Kurt reads its declarations when it starts,
before anything else, and freezes them (only the parse rule of `local` and the
internal marker of bound variables are made in `kurt.py`). It is never `load`ed --
`load minimal` is an error ("is the core, which every file starts with"). It deliberately declares no aliases:
`propositional.kurt` supplies `⊤`, `⇒`, `∧`, `∨`, and `¬`, and `logic.kurt` supplies `∀` and `∃`.

### 8.2 `load` and the theory library

    load NAME               ; load "path/to/name.kurt"
    load NAME1, NAME2, ...

`load` searches, in order: the loading file's own directory (or the
current directory, from the CLI/shell), then any `-p`/`--path` directory
given on the command line, then Kurt's own packaged theories
(`src/kurt/theories/`). The `.kurt` extension is added automatically if
missing. The packaged theories can't be shadowed: `load propositional` always loads
Kurt's own `propositional.kurt`, and a file `propositional.kurt` found earlier on the search
path is an error (rename it) — `def`, and the checks built on the packaged
theories, rely on their exact content. (A name with a directory, `load
./propositional` or `load lib/propositional`, is your own file, as written — not trusted, so
under `--strict` it may not `use` anything.)

The symbols declared by a *trusted* theory file — one that comes with Kurt,
or one found via `-p DIR` — are **frozen**: no other file can declare them
`flat` or `sym`, or put them into a `chain` in a way that
derives something new about them. E.g. `chain ≠` (which would make `≠`
transitive) is rejected, while `chain = lt` for a file's own relation `lt`
is fine: a frozen operator may be combined with the file's own operators
if the frozen ones come first (the chain's conclusions use the later
operator) and are already chained that way in their theory. A file that has *already finished* loading is not loaded again
(tracked via `get_load_level`, per level, inherited from parent levels) —
so `load propositional` twice in a row, or from two different files that both
depend on it, is a harmless no-op (logged as `already loaded, skipped`)
rather than a duplicate-axiom error. A
file that is still *in the middle* of loading (a genuine cycle: `a.kurt`
has `load "b.kurt"`, and `b.kurt` has `load "a.kurt"`) is tracked
separately and raises a clean `EvalError: circular \`load\`: ...` instead
of recursing forever. The end of a loaded file closes the blocks still open
in it, as a dedent does (§7, §9): an `assume`/`let`/`pick`/`case` gives its
result, a `sandbox` is discarded -- nothing half-open leaks into your file. A
`proof` whose goal isn't reached by then, or a `show` without a proof, fails
the whole `load`.

**Each file is checked on its own.** A loaded file is checked in a fresh
context, one level deep, inside an implicit `sandbox` of its own (which `break`
can't close and `summary` doesn't list; the main file is checked the same way):
the hard-coded core (§8.1) and the files it loads itself -- nothing
of the file that loads it, not its facts, declarations, or `calc on`. So a
library can't use a fact without loading the file it comes from, and the
order of two `load`s doesn't change what either of them proves. What the file
exports (below) is then added to the loading file. A symbol that both know
must mean the same there: its declarations may not contradict each other
(one side may have more, e.g. numbers.kurt binds `=` of equality.kurt to the
calculator), and if it is defined by a `def`, it must be the same `def` on
both sides -- a `def` is only conservative for a new symbol, so
`const f` / `use f = 1` here and `def f = 2` in the loaded file is an error.
A fact that two loaded files both pass on (from a file both of them load)
is added once.

**A symbol is declared by one file only.** The declarations of a symbol --
`infix`, `prefix`, `postfix`, `arity`, `brackets`, `bindop`, `flat`, `sym` --
come from the one file that declares it; Kurt remembers which (it travels
with the exports). If two different files declare the same symbol, they
can't be loaded together, in either order, directly or through other files:

    EvalError: `+` is declared in `numbers.kurt` and in `field.kurt` -- a symbol
    is declared by one file only, so these two can't be loaded together

The reason: a theory's laws hold for everything written with its operators.
numbers.kurt says `$a * $b = $b * $a` for every `$a`, `$b`; a theory of
matrices that declares its own `·` or `+` must not get those laws. So:

- numbers (ℕ, ℤ, ℚ, ℝ): `load numbers` (or `natural`, `integer`, `rational`,
  `analysis`, which load it);
- linear algebra: a structure that declares its own operators, like
  `field.kurt`, `vectorspace.kurt` (and `proofs/mafi1/matrices.kurt`) -- not
  together with numbers.kurt;
- `group.kurt` takes its operation as an argument (`group(G, (∘), e, inv)`),
  so it goes with either.

**A theory loads what it uses.** A file gets the symbols of the files that
its loaded files load, too: after `load natural`, `∀` (from logic.kurt) and
`+` (from numbers.kurt) are there. But a theory that relies on this breaks
when the file in between stops loading them. So a trusted theory -- one that
comes with Kurt, or one from a `-p` directory -- gets a note for a symbol of a
theory it doesn't load itself:

    ; note: `forall` comes from `logic.kurt`, which this file doesn't load itself --
    ; `load logic` makes it independent of what the other files load

The theories that come with Kurt load everything they use (a test checks
it). For a proof, this isn't noted -- `load numbers` and then `=` is fine --
but `kurt --deps` lists such symbols for any file (§1).

The same file reached twice (two files both load numbers.kurt) is one
declaration, not two. (numbers.kurt used to be called `arith.kurt`.) In one run of Kurt, a file is checked once and its exports
are reused, as long as neither it nor a file it loads changed; only the
file you check itself is always checked again (it prints its steps).

The packaged theories (`src/kurt/theories/`), and roughly what each adds,
declaring their own prerequisites via their own `load` lines:

| theory | adds | depends on |
|---|---|---|
| `propositional.kurt` | `or`, `not`, `iff`, `invimplies`, `false`; aliases `⊤`, `⇒`, `∧`, `∨`, `¬`; and-elim, or-intro/elim, iff-intro, iff-elim-forward/backward, not-intro/elim, bottom-intro/elim | (none — builds on the hard-coded core) |
| `equality.kurt` | `=`, `≠` (`a ≠ b` is read as `¬(a = b)`, `inline`); equal-intro/elim | `propositional` |
| `logic.kurt` | aliases `∀`/`∃`; forall-elim, exists-intro, the rules for quantifiers with a condition (§4.4), and rewriting under a quantifier ("forall-iff", "exists-iff": from `∀ x (A ⇔ B)`, `(∀ x A) ⇔ (∀ x B)`); the quantifiers `forall`/`exists` themselves, with their roles (§8.1); unique existence `∃! x P(x)` (`existsunique`, below) | `propositional`, `equality` |
| `objects.kurt` | the sorts of the objects (§5.2): `sort set real` (every number is a set; an object of no sort is any object); loaded by set.kurt and numbers.kurt | (none) |
| `set.kurt` | Zermelo-Fraenkel-style: `in`/`∈`, `⊂` (`A ⊃ B` read as `B ⊂ A`, `x ∉ A` as `¬(x ∈ A)`: `inline`), `∪`, `∩`, separation `{ x ∈ A \| ... }` (no unrestricted `{ x \| ... }`, which would allow Russell's paradox; "separation-in": an element of a part of `A` is in `A`), sets by their elements `{a, b}` ("singleton", and generated rules, §10), `∅` (also `{}`), `Pow`, ordered pairs and tuples (`(a, b)`, "pair-eq", `fst`, `snd`), Cartesian products `A × B`, mappings as sets of pairs (`f ∈ (A → B)`: `f ⊂ A × B` with one pair `(a, f a)` for each `a ∈ A`), "apply", "apply-in", "function-extensionality" | `equality`, `logic`, `objects` |
| `numbers.kurt` | arithmetic; the order (`<`, `<=`; `>`, `>=` are read as them, `inline`); its symbols are numbers (`default real`) | `equality`, `objects` |
| `natural.kurt` | natural numbers (`set Nat`, `ℕ`), the set of all numbers `Real` (`ℝ`) with "ext-real" (two sets of numbers with the same numbers are equal), induction (for a variable that is a number: `default real`); `0 <= n`, the predecessor, no number between n and n + 1, the well-ordering principle (proven from induction); `even` and `odd` (every number is one of them, none both); divisibility `∣` (`\mid`), `coprime` | `set`, `numbers`, `logic` |
| `integer.kurt` | integers `Int`: the natural numbers and their negatives, closed under `+`, `-`, `*` | `natural` |
| `rational.kurt` | rationals `Rat`: m / n with m ∈ `Int`, n ∈ `Nat`, n ≠ 0; closed under `+`, `-`, `*`, `/`; "lowest-terms": a positive rational is m / n with coprime m, n (proven from the well-ordering) | `integer` |
| `group.kurt` | groups: `group(G, (∘), e, inv)` defined by `closed`, `associative`, `identity`, `inverse`; rules for single steps ("group-associative", "group-right-inverse", ...); theorems: the identity and the inverse are unique, `inv (inv a) = a`. Also `abelian(G, (∘))` and `abeliangroup(G, (∘), e, inv)` (`group` and `abelian` together), with "abeliangroup-commute". `∘` is an operator variable, so it all holds for any group, e.g. `group(R, (+), 0, (-))` | `set` |
| `field.kurt` | a field `K` with `+`, `·`, `-`, `inv`, `0`, `1` (`+` flat and sym, `·` flat): every axiom for the elements of `K` (`$a ∈ K`), the (K1)-(K9) of the mafi1 lecture with English names ("plus-commutative", "distributive", ...); theorems: the identities and inverses are unique, `0 · λ = 0`, no zero divisors, `x² = 1` only for `±1`; subtraction `λ - μ` with "minus-def", "minus-minus", "minus-of-plus", "minus-of-minus"; "zero-plus", "times-one", "minus-distributive" (`λa − μa = (λ − μ)a`), "difference-nonzero" (`a ≠ b ⇒ a − b ≠ 0`), "product-one-nonzero" (`a · b = 1 ⇒ a ≠ 0`). Its own `+`: not together with numbers.kurt | `set` |
| `vectorspace.kurt` | vector spaces over `K`: `vectorspace($V)`, the (V1)-(V8) for the elements of `$V`; `+`, `·`, `-`, `0` shared with the scalars; theorems: the zero vector and the inverse are unique, `0 · x = 0`, `(-1) · x = - x` | `field` |
| `matrix.kurt` | vectors and matrices as literals (`[1, 2]`, `[[1, 2], [3, 4]]`, one row per line), computed exactly with `calc on`: `+`, `-`, `·`, `transpose`, `det`, `=`, `≠` (and `/` of numbers). Its own `+`: not together with numbers.kurt | `equality` |
| `analysis.kurt` | subtraction for ε/2 arguments ("sub-def": `a - b = a + (-b)`, "sub-split", "sub-add", "sub-mul", "sub-zero", "double", "halves", "le-mul-nonneg"), `abs`, finite sums `sum i (a, b) T`, `max`/`min` and `sup`/`inf` of `T` over the `v` with a condition, `argmax`/`argmin` over a set (*some* place of the maximum, `argmax $v ∈ A T`), limits `lim v a T` (also with a condition, `lim $v > 0 0 T`) by ε and δ; only introduction rules, since these functions give a value also where the maximum, supremum, or limit doesn't exist; `tends v a L T` ("T tends to L for v → a": the limit exists), "tends-def", "tends-lim", "tends-unique" and the limit laws ("tends-add", "tends-mul", ...) | `natural` |
| `continuity.kurt` | only the definitions of `cont x a T`, `diff x a T`, `deriv x a T` by ε and δ ("cont-def", "diff-def", "deriv-intro"), which derivative.kurt loads -- without the rules, a proof goes through ε and δ; "cont-tends": continuity by `tends` | `analysis` |
| `sequences.kurt` | sequences and series: `converges n L T` (by ε and N), its value `seqlim n T`, "converges-unique", the limit laws, "archimedes"; `series i a T` (the limit of the partial sums, "series-def", "series-intro"), the geometric series ("geometric") | `analysis` |
| `derivative.kurt` | continuity `cont x a T`, differentiability `diff x a T` and the derivative `deriv x a T` (of `T` in `x` at `a`), defined by ε and δ ("cont-def", "diff-def", "deriv-intro"); the rules of differentiation (constant, `x`, sum, difference, constant factor, product, quotient, natural powers, chain rule), each with the differentiability it needs; differentiable implies continuous; Fermat ("deriv-max", "deriv-min"), the mean value theorem | `continuity` |
| `integral.kurt` | the Riemann integral `integral x (a, b) T` and `integrable x (a, b) T`: its value as the limit of Riemann sums (for an integrable `T`), continuous functions are integrable; linearity, constants, splitting the interval, `(b, a)`, monotonicity; the fundamental theorem of calculus, both parts ("ftc-diff", "ftc-deriv", "ftc") | `derivative` |
| `modal.kurt` | classical normal modal logic T: formulas are terms built with `→`, `⇔`, `∧`, `∨`, `¬`, `□`, `◇`, `⊥`; `⊢ A` says that A is a theorem, `empty ⊢ A` the same with an empty list of assumptions; the propositional rules for theorems, K, T, duality, distribution, modus ponens, and necessitation | (none) |
| `lambda.kurt` | simply typed lambda calculus: complete syntax-directed typing for a de Bruijn representation, readable named binders `λ`, compatible beta reduction `↦`, and call-by-value evaluation `⇝` | (none) |

`modal.kurt` is the packaged modal theory. A modal formula is a non-Boolean Kurt
term, so its metavariable is `$A`; object connectives such as `→`, `∧`, and `□` only construct
such terms. The Boolean
judgment `⊢ $A` says that the term is an object-level theorem. Therefore necessitation is the
ordinary Kurt schema `(⊢ $A) implies (⊢ □$A)`, while object modus ponens has the two Kurt premises
`⊢ $A` and `⊢ ($A → $B)`. The turnstile is declared both prefix and infix: prefix `⊢ A` means
theoremhood, binary `G ⊢ A` means derivability from a represented context, and two explicit rules
identify prefix theoremhood with `empty ⊢ A`. `proofs/logic-encodings/` contains a small sequent
calculus and an ordered-resource experiment without exchange, weakening, or contraction.

`modal.kurt` declares the optional sort `formula` for the formulas of modal logic, so a modal
formula can't be written as a claim by itself (`use □P → P` is an error) -- a claim is `⊢ A`,
"A is a theorem". The theory still owns `→` and `□`, so it cannot be loaded together with
`set.kurt` (where `→` is a function-space constructor) without future namespaces.

The former shallow theory with the same filename could not express sound necessitation because
its formulas were Kurt Booleans: `%A implies □%A` also applied below an assumption. It was
replaced. Moving the pretty aliases out of the minimal core lets the current `modal.kurt` own the
paper symbols `∧`, `∨`, and `¬` as formula constructors without changing their role in
`propositional.kurt`.

`lambda.kurt` is another deep embedding. Its `type`, `term`, `index`, `ctx`, and `typing` sorts reject
malformed typing judgments before proof search. De Bruijn terms `at zero`, `at (succ zero)`, and
`abs A M` give complete variable, weakening, abstraction, and application rules using explicit
contexts. Those judgments have the conventional surface `Γ ⊢ M : A`; the older prefix form
`has Γ M A` remains available for compatibility. The theory also provides readable named terms:
`λ` is a real Kurt binder, so
alpha-equivalent terms match, and its `beta` rule uses `sub` for capture-avoiding substitution.
Compatible application rules give weak beta reduction `↦`; `⇝` is a deterministic left-to-right
call-by-value relation with explicit values. The executable examples include a concrete
preservation instance and a finite confluence diamond. General preservation and Church–Rosser
need induction over encoded derivations (and a substitution lemma or parallel reduction), which
the current first-order theory does not supply automatically.
Pure Kurt currently expresses several sound named typing conveniences rather than the full named
hypothetical-context abstraction rule; the de Bruijn representation supplies the general rule
without extending the language. See `tutorial/27-type-and-reduce-lambda-terms.kurt`.

`load` with no arguments lists every file loaded so far, level by level.

#### What gets exported

Not everything a loaded file declares becomes visible to whoever loads it.
A `use`/`def` axiom or a proved (`show`/`proof`/`qed`) theorem is
**exported** exactly when it carries a label and that label isn't marked
`local` (§6.2) — an unlabelled fact, or one labelled `EXPR local "..."`,
stays entirely inside the file that wrote it. A symbol is exported when an
exported fact mentions it, or when the file declares it at its top level:
a declaration written out there (`const`, `prop`, `infix`, `prefix`,
`postfix`, `brackets`, `arity`, `bindop`, `flat`, `sym`, `chain`, `alias`,
`tex`, `lean`, a sort's signature) is the file's vocabulary. Either way, all that is
known about the symbol travels along (its arity and shape, fixity, boolean
signature, `tex`, `lean`, ...), so it can still be parsed and type-checked
downstream. Not exported are: a declaration with `local` at its end
(`const helper local`, `prop Q, R local` -- for the whole line), a
declaration inside a block, `var` (a loaded `var x` would make the loader's
`x` a variable), and the constants Kurt adds by itself at a symbol's first
use (`; added constant`). So a symbol that only ever appears in local facts
and isn't declared at the top level (or only with `local`) is invisible
from outside, freeing up its name for something else entirely unrelated in
whatever file loads this one; a `local` declaration of a symbol that an
exported fact needs still goes along with that fact. (Before 0.9, a
declaration alone exported nothing.) A symbol bound to the calculator (`builtin + add`, §10) is exported too, even
without a fact that mentions it: the binding is an axiom about it (`1 + 1 =
2`, ...) -- e.g. matrix.kurt's literals `[ ]`, `det`, `transpose`. An
alias (`alias`) travels automatically with whatever symbol it names, since
an alias never itself appears written out in a formula — axioms are always
written with the canonical name.

This makes `def`'s two halves — the new symbol, and the fact defining what
it means — travel together when exported. If a `def` is marked `local` but
some *other*, exported fact in the same file still needs that symbol, the
file fails to load with a clear error naming the symbol, rather than
silently promoting the `local` marking away or silently leaving the symbol
meaningless downstream.

The `var` declaration itself is file-local regardless of labelling. Before a formula is stored,
however, each of its declared free variables is replaced in the formula's proof representation
by a fresh internal schema variable. Its local inferred type does not occupy the printed name in
the loading file. Therefore a labelled exported formula remains schematic:
`var p, q` followed by `use p and q "pq"` can match `A and B` after `load`, even if the loading
file uses the printed names `p` and `q` as constants. This also applies to variables in function,
infix, prefix and postfix operator position. Parser-facing declarations such as `arity f 1` and
`infix ∘ 70 70` still travel so the notation remains writable, but the variable role does not.
The original expression is retained for source and normal display; generated internal names
never become part of Kurt source. Normal output makes this conversion visible beside the
original `use` as `; schema: ...` (§6.2), using stable `$`/`%` names instead of the internal fresh
names.

Example:

    ; helper.kurt
    load propositional
    prop P
    prop Q local                     ; the declaration stays inside helper.kurt
    use P            "exported"      ; travels to whoever loads helper.kurt
    use Q            local "hidden"  ; stays inside helper.kurt
    def R iff P      "also exported" ; R travels too, since it's labelled

    ; main.kurt
    load helper
    P                 ; fine -- P was exported
    R                 ; fine -- R (and its definition) was exported
    Q                 ; ProofError: can not derive `Q` -- never exported, so as far as
                      ; main.kurt is concerned `Q` is just a fresh symbol with no axiom
                      ; behind it (§3.4), not literally an "unknown symbol" error

#### `save`: keep a shell session as a file

    save "path/to/file.kurt"

Writes the input lines that were accepted so far to `path` (relative to the current working
directory): in the shell, the session without the lines that failed, and without the ones that
only show something (`theory`, `cert`, `help`, a declaration without arguments, ...); in a file,
its lines so far. The result is ordinary Kurt source, which proves its results again when it is
checked, and gets its certificates in a `.kurtc` then (§1) -- nothing is taken over as an axiom.
`save` needs all blocks closed and no pending `show`, since otherwise the saved file wouldn't
load. `load` lines are kept as typed, so a saved file finds its theories as the session did
(e.g. relative to the working directory). The name must end with `.kurt` and not be the name of
a theory that comes with Kurt, and `save` works neither with `--strict` nor in a loaded file --
it writes the checked file's (or the shell's) own lines, nothing else.

## 9. Blocks and natural deduction

Every open `proof`/`assume`/`case`/`let`/`pick`/`sandbox`/`expect` pushes a
new **level** onto the knowledge base. `summary` prints where the proof is:
the open blocks with what opened them (`; open: case A`), the claims of open
`show`s still to prove, the latest facts, and what could come next -- the same
view that `breakpoint` and `kurt -i` show after stopping (§10), and that the
playground and the editors use. `list` has a different job: it inspects declarations and facts
retained from loaded theories. A
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
content into `kurt -i` behaves the same as running it as a file. To help
with typing, the shell (at a terminal) starts each line with the indentation
of the current block, one level (four spaces) deeper after a line that opens a
block; a backspace over the indentation dedents by one level. The shell edits
its lines itself, the same on macOS, Linux and Windows (no `readline`): ←/→,
Home/End, Delete, Ctrl-A/E/K/U/W, the history with ↑/↓ (kept in
`~/.kurt_history`), Ctrl-R to search it, Tab (below), Ctrl-C drops the line,
Ctrl-D on an empty line ends the shell; a long line wraps, and pasted lines
are read one after the other. Not at a terminal (a pipe), it reads plain
lines. Two
keywords remain as *optional* alternatives to dedenting, and work
identically in files and the shell: `qed` (§7 — still needs a real dedent,
but also checks you're closing a `proof`) and `break` (§9.5 — needs no
dedent at all, and is the only way to close a `sandbox` other than
dedenting past it).

**Running a file itself already starts one level deep, inside an implicit
`sandbox`** (the same mechanism `load` uses, see §8.2); `summary` doesn't
list that one.

### 9.1 `assume` and `case`

    assume EXPR
        ...
    (closes by dedenting, or `qed`/`break`)

Opens a block that adds `EXPR` as a local axiom; for a conjunction `A ∧ B`,
its parts are facts too, shown as derived lines `6a A`, `6b B` ("and-elim";
also for `case` and `pick ... with A ∧ B`). Closing it derives
"impl-intro": whatever you proved last inside the block becomes `EXPR
implies <that>`, on the parent level. If the last thing derived inside the
block was literally `false`, closing *additionally* derives `not EXPR` via
"not-intro" (both formulas are added). Inside the block, the free variables
of `EXPR` are *fixed*: in `assume P $x`, `$x` is one arbitrary object, the
same in every line of the block -- so `P $x` follows, but not `P $y`. Closing
the block generalizes again: `P $x implies ...` holds for every `$x`. `case` closes like
`assume`: a sequence of `case`s produces one `EXPR implies <goal>` for every branch. On the final
explicit goal, Kurt looks for a flat `or` fact and exactly one such implication for every
alternative. This shortcut is available only when the theory contains the general binary
`or-elim` schema; it does not assign a built-in meaning to an operator merely named `or`. A
dedicated `case-elim` certificate records that rule and the finite list, and the independent
kernel checks both. This works for any number of alternatives without generating a schematic
n-premise rule or searching a Cartesian product of facts. The disjunction itself must already be
derivable/`use`d, and every branch must have the same goal. Forgetting a branch, the disjunction
fact, or the final explicit claim is the most common way a `case` proof silently doesn't finish — it fails with an
ordinary "can not derive" on that final line, not a `case`-specific error.

The running time of `case` (measured with `scripts/bench_case.py`, 2026-10-09, see
dev/lab-notes.md): the final `case-elim` step itself is cheap and grows about
quadratically with the number n of alternatives -- about 50 ms for n = 128 -- and it is always
`case-elim`, never a combination the general search finds. The blocks are ordinary lines,
though: if every block derives the goal with one of n rules that all have the goal as their
conclusion, each block's search tries all of them, and the whole proof grows about cubically
(about 0.2 s for n = 16, 5 s for n = 64, 40 s for n = 128 on a slow machine). For proofs with a
handful of cases this doesn't matter. For very many cases, implications that name their case
(`A3 implies G`, stated or proven) are fast: then `case-elim` uses them directly, without
blocks (0.4 s for n = 128).

### 9.2 `let`

    let SYMBOL             ; or a comma-separated list: let x, y, z
    let CONDITION           ; e.g. let x>0
    let SYMBOL with CONDITION   ; the same, naming the constant, e.g. let x with P(x)
        ...

Introduces one or more brand-new constants (each must not already be a
declared constant). A condition (`let x>0`) also `use`s the condition as a
local axiom, in one step. Closing the block derives "forall-intro": the
last thing proven inside becomes universally quantified over each new
constant, in reverse declaration order, skipping any that turn out to be
boolean variables. `let x with C` is `let C`, with the constant named: it
is rejected if `C` is about another symbol.

`let` and `pick` take their conditions the same way, but they are opposite
rules: `let` *assumes* the condition for an arbitrary `x` and gives "for all
x" (∀-introduction); `pick` needs a known `∃` and gives a witness
(∃-elimination). A `pick` without a matching `∃` says so, and suggests `let`.

### 9.3 `pick`

    pick SYMBOL with FACT
    pick FACT              ; the same, with the SYMBOL that FACT is about, e.g. pick c > 0
        ...

Requires some already-known formula `exists $x P` in the theory such that
substituting the new `SYMBOL` for `$x` in `P` gives exactly `FACT` -- or one
that follows in one step, which Kurt then shows as a derived line `13a` before
the `pick` (e.g. from `P(c)` and a rule `P($x) ⇒ ∃ y (Q y)`, `pick b with Q(b)`
derives `∃ b (Q b)` first). If found, it opens a block with `SYMBOL` as a new constant and `FACT` as a local
axiom. Closing the block derives "exists-elim": the last formula proven
inside must not mention `SYMBOL` (checked, and also not mention any other
constant introduced on the block's own level) — with that check passed, it
becomes the block's result on the parent level, without any reference to
the witness.

From an existential with a condition, `exists $x > 0 P($x)` (§4.4), `FACT` is the condition and
the body for the witness: `pick c with c > 0 ∧ P c` -- as logic.kurt's "exists-cond-def" says,
`∃ (sub $x $v %C) %P` is `∃ $w ((sub $x $w %C) ∧ (sub $v $w %P))`, so no detour through that
rule is needed.

`SYMBOL` must be a bare new-or-existing name, unlike `let`'s otherwise
similar `let SYMBOL` / `let SYMBOL>0` (§9.2) — a `pick`ed witness can never
carry an extra condition of its own the way a `let`-bound one can: `let`'s
condition becomes an assumption that gets quantified away when the block
closes, but a `pick`ed witness is existential, so an unearned extra
condition on it would just be an unproven fact about a specific value, not
a sound derivation. `pick x>0 with FACT` is therefore rejected outright
(`EvalError`) rather than silently accepted or silently ignored; the
witness's only property comes from `FACT` itself. Without `with`, as in
`pick c > 0`, the whole line is the `FACT` (as `let c > 0` is the condition),
and the witness is the one new symbol it is about.

### 9.4 `sandbox`

    sandbox
        ...
    (closes by dedenting, discarding everything inside -- or by `break`, immediately)

A scratch block: everything inside is discarded by default, never merged
into the surrounding theory, whether it closes by dedenting (§9's
introduction) or by `break` (§9.5) right away. The end of the file closes
a `sandbox` still open there like a dedent, discarding its content
(`sandbox ; 5 closed, its content is discarded`).

### 9.5 `break`

    break     ; discard the current block immediately, without proving anything

`break` closes the current block right away, discarding it — no
`impl-intro`, `forall-intro`, etc., nothing is added anywhere — without
needing to dedent past it first. Works identically in a file or the
interactive shell, and on any open block: it gives up the innermost open
thing. Breaking out of a `proof` gives up only that attempt: the `show` it
was trying to prove stays open, and a new `proof` can follow. Right after a
`show`, or after the `break` of its `proof`, no block is open for the claim,
so `break` withdraws the claim itself — `break`, `break` gives up a proof
completely. A withdrawn claim is still to do: the file ends with "Proof
almost checked" and the claim among its `todo`s (it is not complete, for
`--json` and the grader). A claim that is neither proved nor withdrawn is an
error at the end of the file ("has no proof"). (Before 0.9, the first `break`
withdrew the claim too.)

`break` can't close the file's own implicit top-level scope (§8.2, §9's
introduction) — there is no real, user-written block there to close, so it
raises a clean error rather than doing anything to it.

### 9.6 `expect`

    expect "KIND"
        ...
    expect "KIND" "TEXT"
        ...

Opens a block whose content is *expected to raise* an error of the given
`KIND` (and, with `TEXT`, whose message contains `TEXT`). The kinds, each
for one stage of reading and checking a line:

| kind | when |
|---|---|
| `ScanError` | a symbol can't be scanned (an unknown character, a number with too many digits) |
| `ParseError` | the line can't be read: brackets, indentation, a chain's continuation, an incomplete expression |
| `EvalError` | the line is readable, but the statement isn't allowed: wrong arguments of a keyword, conflicting declarations, `load` problems, a claim that isn't boolean |
| `TypeError` | sorts, the arguments of `sub`, the variable or condition of a binder |
| `ProofError` | a claim can't be derived, a block can't close as it should |

(Every `KurtException` carries its `.kind`, see `KurtException.KNOWN_KINDS`
in `kurt.py`.) If something inside the block
raises exactly that kind, the whole block (including anything it did) is
discarded and checking simply continues with the next statement, the same
way `break` discards a `sandbox`. If the block closes normally with nothing
having raised, *that itself* is now the failure (`ExpectationError: this
\`expect "KIND"\` block finished without raising a \`KIND\``); if something
raises but of the *wrong* kind, that's also a failure, reported with both
kinds shown.

This exists so a proof file (or a lesson, see `keywords/16-expect.kurt`) can
demonstrate a mistake and have Kurt itself confirm it still fails the
expected way, rather than relying on a comment nobody re-checks, or on a
separate test harness matching exact (and therefore fragile — see
`dev/todo-claude.md`) error text.

The expected error may come from anywhere inside the block: from a
statement directly inside it, from inside a nested block (`assume`,
`proof`, another `expect`, ...), or while such a nested block closes (a
failing `qed`, or the dedent that closes a `let`/`pick`/`proof`). In the
last case the line that triggered the dedent is already outside the
`expect` block, so it is still evaluated afterwards. Any lines of the
block after the one that raised the error are skipped. Since the content
of an `expect` block is always discarded, `use` is allowed inside it (see
§6.2). A second string is a text that the error message must contain:
`expect "ProofError" "can not derive"` (a string can't contain `"`). A
`break` inside `expect` closes the `expect` block itself; an error that only
a whole file can make (a proof still unfinished at its end, a `show`
without a proof, `break` at its top level, ...) is checked by `expect` around a `load` of such a file (see
`tests/how-to-write-test-proofs.md`).

## 10. Session toggles and output

    format sexpr | normal | source     ; stored tree, readable normal form, or source spelling
    hint on | off                  ; in the shell: before each prompt, what could come next
    calc on | off       ; a step may follow by computing with numbers (the symbols bound with `builtin`)

Each, called with no argument, reports its current setting instead of
changing it (`format` also names the other options).

`format normal` is the default readable form and reflects Kurt's stored normal form;
`format sexpr` exposes the exact expression tree. `format source` replays the input spelling
saved on a stored formula (aliases, parentheses and operand order included); an expression that
was generated internally and has no independent source spelling uses normal formatting. Editors
should use structured API/LSP data when they need positions rather than parsing any display.

**What `calc` computes** is said by the theories: they bind their symbols to
Kurt's built-in calculator, whose operations are `add`, `subtract`, `negate`,
`multiply`, `divide`, `power` and the comparisons `eq`, `ne`, `lt`, `le`, `gt`,
`ge`. numbers.kurt does

    builtin + add, - subtract, - negate, * multiply, / divide, ^ power
    builtin = eq, < lt, <= le

(`>`, `>=` and `≠` are read as `<`, `<=` and `¬(… = …)`, `inline` §6.2; the
negation of a computed comparison holds by calc, `¬(2 = 3)`)

and a symbol that isn't bound is never computed. Sets of numbers, too: the
calculator knows `naturals`, `integers` and `rationals`, natural.kurt does
`builtin Nat naturals` (integer.kurt and rational.kurt likewise for `Int` and
`Rat`), and set.kurt `builtin in element`; then `calc on` proves `3 ∈ Nat` and
`-3 ∈ Int`, but not `-3 ∈ Nat`.

**`builtin`** gives a symbol a meaning that Kurt itself implements: a
calculator operation, as above, or a **role of the engine**. The engine
gives no symbol a meaning by its name alone -- only the roles that the
theories assign:

| role | in | what the engine does with it |
|---|---|---|
| `equivalence` | propositional.kurt: `builtin iff equivalence` | a fact `A iff B` is used as `A implies B` and as `B implies A`; `def` may define with it |
| `disjunction` | propositional.kurt: `builtin or disjunction` | `case` blocks for the alternatives of a fact `A or B or ...` close by "case-elim" (with propositional's "or-elim") |
| `negation`, `falsum` | propositional.kurt: `builtin not negation, false falsum` | an `assume A` block whose last line is `false` also gives `not A` ("not-intro") |
| `equality` | equality.kurt: `builtin = equality` | `def` may define with it |
| `universal`, `existential` | logic.kurt: `builtin forall universal, exists existential` | the outer `∀`s of a fact are stripped (its variables stand for anything), `let` closes with the universal ("forall-intro"), `pick` opens from the existential ("exists-elim"); they need a binder with two arguments |
| `setbrackets`, `setbuilder`, `emptyset` | set.kurt: `builtin { } setbrackets, \| setbuilder`, `builtin ∅ emptyset` | sets by their elements and by a property: see below |

A role needs the matching `prop` signature (`prop iff 0 1 2`), a role has
one symbol, and only a trusted theory -- one that comes with Kurt, or one
from a `-p` directory -- can assign a role, since it changes what the engine
derives (a calculator operation, like an axiom, also in other files, but not
with `--strict`). So a file's own `iff` or `or`, without propositional.kurt, is just a
relation.

**Sets** (set.kurt, since 0.9): with the roles of sets, braces make three
kinds of terms -- `{a, b, c}` by its elements (`({} a b c)`), `{x ∈ A | P}`
by a property (the set-builder, the `|` term itself; `|` outside braces is an
error), and `{}`, which is `∅`. So a rule about `{$y}`, like set.kurt's
"singleton" (`$x ∈ {$y} ≡ $x = $y`), never reads a set-builder or a list as
its one element (before, it proved `false`, `proofs/soundness/sets-by-their-elements.kurt`),
and `{(a, b)}` is the set with one element, the pair. For each set by its
elements in a line, Kurt adds the rules for it to the file (from the source
`<set enumeration>`, checked by the kernel like any rule): each element is one,
`c ∈ {a, b, c, d}` in one step ("element-3-of-4"), and membership is the
disjunction, `$x ∈ {a, b, c} ≡ $x = a ∨ $x = b ∨ $x = c` ("enumeration"),
which `case` splits -- for a set of constants of the file this rule is of the
set itself, otherwise of its length ("enumeration-n"). The order of the elements
counts for the terms, `{a, b} = {b, a}` follows from "extensionality". About
15 elements take a second or two; a disjunction of twenty or more is slow to
find (dev/todo.md, speed).

With natural.kurt, `...` lists numbers: `{a, ..., c}` in steps of one
("range"), `{a, b, ..., c}` and `{a, b, ...}` in steps of `b - a`, for `a < b`
("progression", "progression-intro", "progression-infinite", ...) -- each
membership is an `∃ k ∈ Nat` (proofs/natural-numbers/progressions.kurt). One
or two elements fix the step; more, as in `{2, 3, 5, 7, 11, ...}`, would only
suggest a pattern, which Kurt can't know, so it refuses them: write a
set-builder, `{p ∈ Nat | prime p}`.

**The set-builder is one construct with three parts:** the variable `x`, the set `A` it ranges
over, and the statement `F` -- "the set of the `x` in `A` with `F`". Kurt writes it with two pieces
of syntax, the braces and the binder `|` (it has no operators of three pieces), and reads it as one
term: the braces are dropped (`set_terms`), and the `|` node remains with two arguments, the binding
condition `x ∈ A` (the variable and its set together, as in `∀ x ∈ A F`) and the body `F`. So the
variable is bound like by any binder (§4.4), the body is a statement (§5.1), and `x` ranges over
the elements of `A`. Without a set, `{x | F}` is refused: unrestricted comprehension would allow
Russell's paradox (set.kurt's "separation" only carves a part out of a given set).

**Vectors and matrices** (matrix.kurt, `load matrix`): a bracket pair bound
to `matrixbrackets` (`builtin [ ] matrixbrackets`, both brackets of a pair declared with
`brackets [ ]`; a bracket pair takes no other role) makes literals of numbers -- `[1, 2, 3]` a row,
`[[1, 2, 3], [4, 5, 6]]` a 2x3 matrix row by row, `[[1], [3], [5]]` a column (a row
`[1, 2, 3]` and the one-row matrix `[[1, 2, 3]]` are the same value)
-- and the operations `add`, `subtract`, `negate`, `multiply` (a number times
a matrix, or a matrix times a matrix), `transpose`, `determinant` and the
comparisons `eq`, `ne` compute them exactly (`/` divides numbers only). Shapes
that don't fit give no value. Written over several lines, each line inside the brackets is a row,
as on paper:

    A = [1, 2, 3
         4, 5, 6]          ; is [[1, 2, 3], [4, 5, 6]]

In normal screen output, a matrix with two or more rows is printed on aligned lines, while row
vectors stay compact:

    [[  1, 20],
     [300,  4]]

This is display only. Saved `.kurt` source keeps the accepted input lines, and `format sexpr`
keeps its one-line structural representation. `format source` shows the spelling originally
entered for a stored formula.

(a line break inside a bracket pair bound to `matrixbrackets` -- `builtin [ ] matrixbrackets` --
without another one in it ends a row; elsewhere it is a space, also inside a
`[ ]` that isn't bound: the theory makes the brackets special, not Kurt). matrix.kurt has its own `+`, `-`, `·`, so it isn't loaded together
with numbers.kurt (§8.2); it computes with literals and has no laws for
matrices written with variables (for those: proofs/mafi1/matrices.kurt, over
a field). As everywhere with `calc on`, a name defined as a matrix
(`def A = ...`) isn't computed in the same line: replace it first, one step
per line.

A binding is like an axiom
(`1 + 1 = 2`, `2 + 1 = 3`, ...), so `--strict` rejects it outside the trusted
theories, and the symbols of a trusted theory can't be bound anew. Numbers
bound to calculator operations are constants: the binding supplies fixed semantics and reports
`const SYMBOL ; added constant` if that role was not already known. A variable or binding
operator cannot also be calculator-bound. Numbers are exact: integers, decimals (`0.1` is
exactly one tenth, so `0.1 + 0.2 =
0.3` holds), and fractions, which stay fractions (`1 / 3 + 1 / 3` is `2 / 3`).
What has no exact value isn't computed: `1 / 0`, `0 ^ -1`, `2 ^ 0.5`, and
`0 ^ 0` (which numbers.kurt leaves open). Neither is a result with more than
1000 digits, and a longer number literal is a `ScanError`.
`0 + x` and `1 * x` are `x`, `0 * x` is `0`. In numbers.kurt, `^` is
right-associative and binds more tightly than the prefix `-`: `- 2 ^ 2` is
`- 4`, and `2 ^ 3 ^ 2` is `2 ^ 9`. A decimal with an integer value is that
integer: `1.0` is `1`.

With `calc on`, a line may follow by computing -- it is not changed: it is
stored as written. It follows if its computed form follows (e.g. `1 + 1 = 2`
is computed to `2 = 2`, by calc), searched with the computed forms of the
facts written with `calc on` -- or, if not, as written (so `(1 + n) * (1 + n)
= 1 * (1 + n) + n * (1 + n)` is an instance of "distrib-add", and from `7 = 1
+ 6` follows `∃ k (7 = 1 + k)`). No symbolic simplification. A comparison of
numbers (e.g. `3 <= 4`, `2 + 2 < 5`) is proven directly "by calc", and a claim
follows "by calc" from a fact that computes to the same thing (e.g. `x = -25`
from `x = (-5) * 5`). (Before 0.9 each line was computed when it was read.) Results of
substitutions (`sub`, as in `induction` or `equal-elim`) are computed too:
substituting `k + 1` into `$x + 1` gives `k + 2`, not `k + 1 + 1`. While
matching a rule, a part of it is computed as soon as its variables have
values: with `$n := 3`, the `($n - 1)!` of "factorial-step" matches `2!`, and
after `def f($x) = $x * $x`, `f(3) = 9` follows in one step. But `calc` doesn't
*solve*: the `$b / $c` of "gt-div-pos" doesn't match `0` while `$b` is still
unknown -- state such steps as their own lines, or use a rule that fits
(like "div-pos"). Nor does it combine a rewrite with a calculation: `x = 6`
doesn't follow in one step from `x = 2 * y` and `y = 3` -- write `x = 2 * 3`
in between, then `x = 6` follows by calc. **Not implemented on purpose:** solving for an
unknown while matching, or several steps at once, doesn't fit the idea that
each line is one step a reader can check (§6.1); the line in between is the
step. `calc on` holds for its block and the blocks in it, and ends with it
(and with its file): after the `qed` of a proof that switched it on, it is off
again (before 0.9 it stayed on). With `hint on`, the shell prints before each
prompt what could come next (`; hint: next, e.g. proof`): `proof` after a
`show`, in a proof its goal and then `qed`, in a chain its relation, in a
`case` block the other alternatives -- Tab on an empty line writes it.

**`breakpoint`**, a line in a proof file: at a terminal (or with `kurt -i
FILE`), checking stops there and the shell continues with that state -- the
open blocks, the facts, what is still to prove; try steps there, then write
the one that works into the file (Ctrl-D ends the shell). Without a terminal
(the playground, Kurt from Python), it shows that state and checking goes on.
In a file that another one loads, it is skipped. After an error, `kurt -i
FILE` likewise continues in the shell at the failing line, with the state
there (`keywords/42-breakpoint.kurt`).

**Tab in the shell** (at a terminal) completes: on an empty line the next step (as `hint`); after `=` with `calc
on` the value (`17*42=` and Tab gives `17*42=714`); a LaTeX shortcut its
symbol (`\forall` and Tab gives `∀`); after `load` a theory or a `.kurt` file
here; otherwise keywords, symbols and labels (`"and-` gives `"and-elim"`).
With several possibilities, Tab writes what they have in common, and a second
Tab lists them. It only writes text; every line is checked as usual.

`help` prints Kurt's own one-line description of every keyword, `help use` the one of `use`.

## 11. Known gaps (so you don't mistake them for bugs in your proof)

- Derivation is single-hop (§6.1) — chain several `A implies B` facts
  manually, one derived line at a time. The one partial exception: two
  facts using operators from the same declared `chain` (§4.6) combine
  automatically in one step (`$a < $b` + `$b < $c` → `$a < $c`, etc.,
  including `implies`/`iff` chains) — but that's still exactly one
  combination, not arbitrary-length automatic chaining.
- `and-elim` needs `load propositional` (or a manual axiom instance) — it is not
  hard-coded the way `and-intro` is (§8.1).
- A custom `brackets` pair does not disappear the way `(` `)` does — it
  stays a real operator, printed as e.g. `[]`/`{}` in s-expression form
  (§4.2).

### 11.1 Not implemented, maybe never

Features that were considered and left out, at least until after 1.0 -- some on purpose:

- **`calc` that solves** (§10): matching `$b / 3` against `0` while `$b` is
  still unknown, or a rewrite and a calculation in one step (`x = 6` from
  `x = 2 * y` and `y = 3`). On purpose: each line is one step a reader can
  check; write the step in between (`x = 2 * 3`, then `x = 6`).
- **`def` by pattern matching on constructors**: `constructors Nat 0, s`
  (`Nat` is built freely from `0` and `s`: every element is `0` or `s n`,
  `s n ≠ 0`, `s` injective), then `def fact 0 = 1` and
  `def fact (s $n) = (s $n) * fact $n` -- a recursive definition that is a
  definition, not an axiom. It would need the patterns to be constructors
  only, not to overlap, and the recursion to be structural (otherwise
  `def f (s $n) = f (s $n) + 1` gives `0 = 1`), and `constructors` is itself
  a claim about `Nat` (to be proven, or allowed only in trusted theories).
  Until then, recursive definitions are `use` axioms with a label (like
  "factorial-step" in numbers.kurt).
- **A normalizer for ring expressions** (like Lean's `ring`): a line "by
  ring" holding if both sides are equal as polynomials, e.g. the `ad - bc`
  computations of 2×2 determinants in one line. It would need a declaration
  of which operators form a commutative ring and a large piece of trusted
  code, and a reader couldn't check such a line by one rule -- the same
  reason as for `calc` that solves. Instead: each rearrangement is a line,
  with the laws of the theory (proofs/mafi1/ does so); missing laws, like
  `$a - ($b - $c) = $a - $b + $c`, belong into the theory.
- **`calc`/`eval` that unfolds a user's own recursive function**: print the
  value of e.g. `fact(3)` by repeatedly applying a function's own axioms
  (`fact-zero`, `fact-step` in numbers.kurt) until none apply, instead of
  only folding the small set of built-in arithmetic operations `calc on`
  already folds. On purpose, for now: those built-ins are hand-coded,
  trusted, and provably terminating; a user's recursive axioms carry no
  termination or confluence check, so an automatic "reduce until done" loop
  over them is a different, riskier kind of automation -- it could loop
  forever on a badly-stated recursion, and printing a trusted answer instead
  of a checked proof would break the rule that every claim gets a reason the
  kernel can check (doc/kurt-soundness.md). Until constructors and
  structural recursion (above) make `def fact` a real definition, write the
  unfolding as an explicit one-step-at-a-time chain instead.

- **Sort parameters** (deferred, 2026-10-20): a structure over a carrier of a sort of its own, e.g.
  the integers as a group, `group(Int, (+), 0, (-))`. group.kurt's rules are over all objects
  (`$a ∈ $G`), and `+` takes numbers, so the instance doesn't fit the sorts. The operator could bring
  the sort along (polymorphic elements `$$a`, the sort of the use fixed by `+`), but group.kurt is full
  of `$a ∈ $G`, which a polymorphic variable may not be in (extensionality over the numbers alone
  would give `∅ = {∅}`), and its definitions would have to be families, one per sort: real sort
  parameters for `def`s and rules, with a soundness argument of their own. Until a course needs it: a
  file about the integers as a group states the group facts it needs for `+` itself (dev/todo.md 40).
- **Two substitutions in one formula** (not wanted, 2026-10-20): `sub $x $T (sub $y $N M)` is refused,
  and so is a `sub` in a goal. The search finds the value and the hole of a `sub` from the goal
  (`sub_solutions`), for one hole; two would make the matching higher-order unification. Only "the
  substitutions commute" needs it, for an older proof strategy -- preservation and Church-Rosser by
  parallel reduction need one `sub` per step (doc/kurt-current-limits.md §2.3).
- **A rule with a hypothetical premise for Kurt's own binder** (not wanted, 2026-10-20): the typing
  rule of a *named* `λ`, `has (extendx Γ x A) M B ⇒ has Γ (λ x M) (fun A B)`, is accepted but can't be
  used -- `x` is the binder of `λ x M` and an ordinary argument in the premise, and when the binder
  matches the goal's name, the other occurrence keeps the rule's own. Making it work would let the
  goal's bound name leave its binder, free in the premise -- the area of capture and eigen variables
  where the worst soundness bugs were -- and it would need a freshness condition Kurt can't state.
  The de Bruijn presentation of lambda.kurt has the general rule without the problem.
- **A second quantifier symbol for `let`** (not wanted, 2026-10-20): `let` closes a block with the one
  universal quantifier, `pick` opens one from the one existential. The sort of a binder distinguishes
  the ranges already (`∀ X` over sets, `∀ n` over numbers; second order as `let X ∈ ℘(Obj)`); a second
  symbol would be a second spelling, and its dispatch by sort would enter the kernel's block rules. A
  different display is notation (`tex`, `inline`).

### 11.2 Why no namespaces (yet)

Two theories loading symbols with the same name can't collide the way `import` does in most
languages: "a symbol is declared by one file only" (§8.2) -- `load numbers, field` simply can't
both declare `+`. Where you would expect to need a namespace -- `group.kurt`, `field.kurt`,
`vectorspace.kurt` each wanting their own `+`/`∘` -- Kurt uses an **operator variable** instead:
their theorems are stated over a schematic `$op` (`var ∘`, `infix ∘`), instantiated at a concrete
operator as an argument (`group(R, (+), 0, (-))`, `tutorial/24`), not as a qualified name. "Which
`+`" is something you pass in, not something you look up.

The one real collision in the bundled theories is `⊢`: `modal.kurt`'s "A is a theorem" and
`lambda.kurt`'s typing judgment `Γ ⊢ M : A` are genuinely unrelated notations that happen to share
a glyph, and only matter if one file loads both. A general lexically-scoped namespace ("open a
block, use a theory's notation inside it, close it, the notation is gone") sounds like the fix,
and the *infrastructure* for it already exists: `KnowledgeBase` is a stack of levels, and a
declaration (`infix`, `bindop`, `arity`, ...) is visible only from the level that made it and its
descendants -- a lookup (`is_infix`, `is_bindop`, ...) walks up `parent`, never sideways or down.

But there's a catch that makes this harder than it looks. When a block closes and one of its
formulas escapes to the surviving level (`assume`'s "impl-intro", `let`'s "forall-intro", ...),
any notation that formula needs travels with it -- the declaration is promoted to the surviving
level, the same way a `load`'s exported facts carry the notation they need (§8.2); otherwise the
surviving formula couldn't be printed or re-parsed. But that also means the declaration is no
longer scoped to the block once *anything* escapes using it: Kurt tracks every symbol "used in a
formula" (parent-chain aware, like the lookups above) and permanently refuses to redeclare it
differently anywhere reachable from that point on (`EvalError: symbol \`...\` has been already
used in a formula, declaring it now would change what that formula means`) -- on purpose, since
silently changing what an existing fact means would be unsound. So "open a namespace, use
conflicting notation, close it, reuse the symbol differently later" does not actually work today
if anything inside the block survives it: the two meanings would need to be two different symbols
internally, not two lexical scopes of the same one.

The smaller fix that's actually in scope is not a general namespace system, but a `load`-site
rename for the rare real collision, so the common case stays exactly as readable as it is now and
only the colliding pair needs one explicit line -- see `dev/todo.md` #21.

Since a grammar declaration inside `assume`/`case`/`let`/`pick`/`proof` was never actually scoped
to the block for the reason above, it is now rejected there outright (§4.1, §6.2), the same way
`use`/`load`/`def`/`chain`/`inline` already were: `infix`, `prefix`, `postfix`, `brackets`,
`arity`, `bindop`, `flat`, `sym`, `alias` and `sort` must be declared at the top level, or inside a
`sandbox`/`expect` whose content is discarded anyway. This closes the one case that used to look
like it worked (nothing escaped the block in the test files that tried it) but was never actually
safe in general.
