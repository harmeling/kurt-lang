# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Kurt is a proof language and interpreter: a small language for writing mathematical proofs in a form close to how humans write them, with automatic checking (designed for students to get immediate feedback, similar to automated testing while learning to program). The entire implementation — lexer, Pratt parser, type checker, and proof engine — lives in one file: `src/kurt/kurt.py`.

## Commands

Setup (editable install with dev extras):

    python -m venv .venv
    source .venv/bin/activate
    pip install -e .[dev]

Run the full test suite (stdlib `unittest`, no pytest):

    python -m unittest

Run a single test file / class / method:

    python -m unittest tests.test_kurt_parser
    python -m unittest tests.test_kurt_proofs.TestProving.test_proving
    python -m unittest tests.test_kurt_lexer -v

Coverage:

    coverage run -m unittest
    coverage report

or, where the `coverage` package isn't installed, with the standard library only (Python 3.12+;
subprocess-based tests of the CLI aren't counted):

    python3 scripts/line_coverage.py            # add --lines to see each missed line

Run the interpreter directly:

    kurt                        # REPL
    kurt path/to/proof.kurt     # check a proof file, exit
    kurt -i path/to/proof.kurt  # check, then drop into REPL
    kurt -d path/to/proof.kurt  # debug output
    kurt -v path/to/proof.kurt  # verbose output
    kurt -s path/to/proof.kurt  # strict, for grading
    kurt --no-kurtc path/to/proof.kurt  # don't write/use the `.kurtc` certificate files
    kurt --deps path/to/proof.kurt      # the tree of loaded files, with their certificates
    python -m kurt path/to/proof.kurt   # the same as `kurt`

A LaTeX document of a proof comes from a separate script, not from Kurt itself:

    python3 scripts/kurt2latex.py path/to/proof.kurt > proof.tex

`kurt.py` is also runnable standalone without installation (`python3 src/kurt/kurt.py`), as long as the `theories/` directory is reachable — this matters because the README documents copying just the single file plus `theories/` for classroom use.

Build the genuinely single-file classroom bundle (`theories/*.kurt` embedded directly, no `theories/` directory needed at all):

    python3 scripts/build_standalone.py       # writes dist/kurt.py

This works via `_EMBEDDED_THEORIES` (empty in `src/kurt/kurt.py`, populated only in the generated `dist/kurt.py`) and the `EmbeddedTheories`/`_EmbeddedTheoryFile` helper classes, which `theory_path` appends as a last-resort search path. `tests/test_standalone_bundle.py` builds the bundle and runs it in a directory with no `theories/` at all to confirm this.

## Proof files as tests (important — read before adding `.kurt` files)

`tests/test_kurt_proofs.py` auto-discovers **every** `.kurt` file under `proofs/` (recursively) plus everything in `src/kurt/theories/`, runs each through `kurt.load_file`, and asserts that the last line of output matches an expected marker. Adding a `.kurt` file under `proofs/` makes it a test case automatically — there is no separate registration step.

- By default, a file just needs to run to completion without raising — no marker needed, whether it's an ordinary successful proof or one that uses `expect "KIND"` internally to check its own interesting condition (see `doc/kurt-doc.md` §9.6). Only add a `;;; ` marker on the file's **last line** (see `tests/how-to-write-test-proofs.md`) when the file's point is a *specific* expected error message or output text, since `expect` only checks the kind of an error.
- `proofs/` = proofs that must currently pass (part of the test suite). `proofs/debug/` holds small regression cases for specific bugs/features; `proofs/soundness/` holds adversarial cases specifically for the inference engine's soundness (see `doc/kurt-soundness.md`) — proof attempts that must be rejected (or, for a false-rejection bug, must now be accepted). `proofs/errors/` exercises the error branches of the implementation (misused declarations and keywords, wrong layout, type errors), one `expect` block per error — the place to add a case for an untested error.
- `proofs-not-yet/` = proofs that are known not to work yet; they are **not** scanned by the test discovery and exist as a to-do backlog for language features.
- `tutorial/*.kurt` are the numbered tutorial lesson files (see `tutorial/plan.md`) and are not part of the `proofs/`-style auto-discovered test set — they carry no `;;; ` marker. `tests/test_kurt_tutorial.py` covers them separately: it only asserts that each lesson still `load_file`s without raising a `KurtException`, i.e. that it hasn't bit-rotted as the language changes, not that its output matches anything specific.

## Internal files

`dev/` holds what is for developing Kurt, not for using it: `dev/todo.md` (the backlog and the
plan to 0.9/1.0), `dev/release-plan.md`, `dev/codex-suggestions.md`, `dev/todo-claude.md`,
`dev/suggestions-claude.md`, `dev/lab-notes.md` (the log of agent sessions and SLURM jobs), and
the author's own notes (`dev/notes-on-*.md`).

## Git workflow

After creating a commit, also push it — but only when the current branch is `agent`. On any other branch (`main` in particular), commit as usual but do not push without being explicitly asked.

## Architecture

`src/kurt/kurt.py` processes a `.kurt` file (or REPL line) in a single pass through four stages, applied incrementally per top-level statement:

1. **Lexing** — `scan_string` turns source text into a token stream (`Token`, `PeekableGenerator`).
2. **Parsing** — a Pratt/TDOP parser (`parse_expression`, `nud`/`led` callables looked up per-token via `KnowledgeBase.get_nud` / `get_led`, binding powers via `get_lbp`). Operator fixity (prefix/infix/postfix/bracket), arity, flatness, and symmetry are all *declared inside `.kurt` theory files* (`infix`, `prefix`, `postfix`, `arity`, `flat`, `sym`, `brackets` keywords) and looked up dynamically from the `KnowledgeBase` — the grammar is not fixed in Python, it's extensible from Kurt source.
3. **Type checking** — `type_check_expression` / `check_bool_sig_*` do a light boolean/non-boolean signature check.
4. **Proof evaluation** — `eval_keyword_expression` dispatches proof keywords (`use`, `show`, `qed`, `def`, `assume`, `let`, `pick`, `proof`, `case`, …). Deriving new facts and closing proof obligations goes through unification/matching (`match_against_sub`, `unify_exprs_with_patterns`, `match_all_theory`) and implication elimination (`impl_elim`, `derive_expr`).

Key data structures:

- `Expr` (`list["Expr"] | Token`) — the universal term representation; a leaf is a `Token`, an internal node is a Python list `[op, arg1, arg2, ...]`.
- `Token` — carries the symbol's `Value` plus source position (line/column/filename) for error reporting.
- `Formula` — a proven/assumed statement in the theory: wraps an `Expr` with its label, reason, source line, and keyword. `Formula.local`/`is_exported()` control whether `load` exports it elsewhere (see below).
- `State` — an immutable-style substitution/binding environment used during matching and quantifier handling (`bind`, `walk`, `occurs`, blocked-variable tracking).
- `KnowledgeBase` (`KnowledgeBase` class, `kb` throughout the code) — the central mutable-ish context: current theory (proven formulas), symbol table (fixity/arity/aliases/bool signatures), and a **level stack**. Proof blocks (`proof`, `assume`, `case`, `let`, `pick`) push/pop levels via `push_level` / `pop_level` / `merge_and_pop`, each level scoping its own local assumptions and constants that get discharged when the block closes (e.g. `assume`/`case` blocks introduce a hypothesis that must be resolved before merging back into the parent level).

Loading and modularity:

- `load_file` checks each file in a fresh context (a copy of `core_kb` plus what the file loads itself, `checked_exports`, cached per run by path and hashes in `_checked_exports`), then checks its `ExportBundle` against the loader (`validate_against_loader`: compatible declarations, the same `def`) and applies it. It resolves `load "foo.kurt"` against `theory_path` (cwd first, then the packaged `kurt.theories` resources) — this is how `.kurt` files pull in reusable theories (see `src/kurt/theories/*.kurt`: `minimal.kurt`, `prop.kurt`, `logic.kurt`, `equality.kurt`, `arith.kurt`, `set.kurt`, `natural.kurt`, `analysis.kurt`, `group.kurt`, `modal.kurt`).
- `merge_and_pop` (called once, at the end of `load_file`) implements *selective export* via an explicit `ExportBundle` (`compute_exports` / `validate_exports` / `apply_exports`) -- only the fields of `ExportBundle` cross a file boundary, a new field of `KnowledgeBase` stays local: only a `use`/`def`/proved-theorem fact carrying a label that isn't marked `local` (`EXPR local "label"`, see `local_led`) is exported to the loading file, along with whatever symbols (`free_symbols`) that fact actually needs — an unlabelled fact, or a symbol only ever used in local facts, stays invisible outside the file that wrote it. See `doc/kurt-doc.md`'s `load` section and `doc/kurt-soundness.md` §7.
- `initial_kb` (module-level) is the pristine starting `KnowledgeBase`; tests `copy.deepcopy` it per test case to avoid cross-test contamination.
- `mainstream` (a bool threaded through most eval functions) distinguishes output that should be printed/logged from output produced while silently loading dependencies.

The kernel: every step the search accepts comes with a `Certificate`, which `kernel_verify` checks again without search (`doc/kurt-soundness.md` §9); a step the kernel rejects raises `KernelError` (stops the file, can't be caught by `expect`), so it also fails the tests. A change to the search that produces a new kind of step needs a certificate for it.

Design rule: the `.kurt` file is the only source of truth. Anything Kurt writes (`.kurtc` certificates, `save` output) must either be Kurt source that is checked again, or hints that the kernel checks again -- never a second copy of facts that is trusted on its own.

Docs worth reading before non-trivial language changes: `doc/kurt-doc.md` (language reference, describes current behavior only), `doc/kurt-soundness.md` (audit of what the inference engine's soundness actually rests on, rule by rule, with pointers to the regression tests in `proofs/soundness/` — read this before touching `eval_done`, `derive_expr`, `impl_elim`, or substitution/capture-avoidance), `doc/kurt-cookbook.md` (task-oriented recipes, one short checked example each), `doc/dev-notes.md` (chronological design-decision diary, not a reference — history of *why*, not a description of *what is*), `tutorial/*.kurt` and `tutorial/plan.md` (hands-on lessons). `dev/todo.md` tracks known-missing features and open design questions; `dev/codex-suggestions.md` is an independent review with detailed implementation briefs (its items are in `dev/todo.md`); `dev/todo-claude.md` and `dev/suggestions-claude.md` are a filtered/verified pass over that backlog plus independent implementation-improvement ideas — check these before assuming something is a bug rather than a documented gap.

## Compute policy (shared node)

Every spawned agent session for this repo runs on `ls8-slurm`, a **shared
login node** — only 8 CPU cores, ~20 concurrent users, no GPU. Never run
heavy computation directly there: anything that would peg a core for more
than a few seconds. Before starting anything nontrivial, check the node
isn't already loaded (`top`, or `uptime` for load average against 8 cores).
This project's own test suite (`python -m unittest`) is lightweight and
fine to run inline, but for any CPU-heavy task, submit it via `srun`/
`sbatch` to the SLURM scheduler instead:
- Check `sinfo -N -o "%N %P %T %C %m %G"` for what's free.
- Ask the user for memory/time-limit requirements if the task didn't
  already specify them.
- Log each submitted job (command, job ID, purpose) in `dev/lab-notes.md`.
- A SLURM time-limit kill only ends that compute job — it does not affect
  this claude session.
