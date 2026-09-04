# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

Kurt is a proof language and interpreter: a small language for writing mathematical proofs in a form close to how humans write them, with automatic checking (designed for students to get immediate feedback, similar to automated testing while learning to program). The entire implementation — lexer, Pratt parser, type checker, and proof engine — lives in one file: `src/kurt/kurt.py` (~4300 lines).

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

Run the interpreter directly:

    kurt                        # REPL
    kurt path/to/proof.kurt     # check a proof file, exit
    kurt -i path/to/proof.kurt  # check, then drop into REPL
    kurt -d path/to/proof.kurt  # debug output
    kurt -v path/to/proof.kurt  # verbose output
    kurt -l path/to/proof.kurt  # emit LaTeX proof document

`kurt.py` is also runnable standalone without installation (`python3 src/kurt/kurt.py`), as long as the `theories/` directory is reachable — this matters because the README documents copying just the single file for classroom use.

## Proof files as tests (important — read before adding `.kurt` files)

`tests/test_kurt_proofs.py` auto-discovers **every** `.kurt` file under `proofs/` (recursively) plus everything in `src/kurt/theories/`, runs each through `kurt.load_file`, and asserts that the last line of output matches an expected marker. Adding a `.kurt` file under `proofs/` makes it a test case automatically — there is no separate registration step.

- The expected output is embedded as the **last line of the `.kurt` file itself**, prefixed with `;;; ` (see `tests/how-to-write-test-proofs.md`), e.g. `;;; Proof checked.`
- `proofs/` = proofs that must currently pass (part of the test suite). `proofs/debug/` holds small regression cases for specific bugs/features.
- `proofs-not-yet/` = proofs that are known not to work yet; they are **not** scanned by the test discovery and exist as a to-do backlog for language features.
- `tutorial/*.kurt` are the numbered tutorial lesson files (see `tutorial/plan.md`) and are not part of the auto-discovered test set.

## Architecture

`src/kurt/kurt.py` processes a `.kurt` file (or REPL line) in a single pass through four stages, applied incrementally per top-level statement:

1. **Lexing** — `scan_string` turns source text into a token stream (`Token`, `PeekableGenerator`).
2. **Parsing** — a Pratt/TDOP parser (`parse_expression`, `nud`/`led` callables looked up per-token via `KnowledgeBase.get_nud` / `get_led`, binding powers via `get_lbp`). Operator fixity (prefix/infix/postfix/bracket), arity, flatness, and symmetry are all *declared inside `.kurt` theory files* (`infix`, `prefix`, `postfix`, `arity`, `flat`, `sym`, `brackets` keywords) and looked up dynamically from the `KnowledgeBase` — the grammar is not fixed in Python, it's extensible from Kurt source.
3. **Type checking** — `type_check_expression` / `check_bool_sig_*` do a light boolean/non-boolean signature check.
4. **Proof evaluation** — `eval_keyword_expression` dispatches proof keywords (`use`, `show`, `qed`, `def`, `assume`, `let`, `pick`, `proof`, `case`, …). Deriving new facts and closing proof obligations goes through unification/matching (`match_against_sub`, `unify_exprs_with_patterns`, `match_all_theory`) and implication elimination (`impl_elim`, `derive_expr`).

Key data structures:

- `Expr` (`list["Expr"] | Token`) — the universal term representation; a leaf is a `Token`, an internal node is a Python list `[op, arg1, arg2, ...]`.
- `Token` — carries the symbol's `Value` plus source position (line/column/filename) for error reporting.
- `Formula` — a proven/assumed statement in the theory: wraps an `Expr` with its label, reason, source line, and keyword.
- `State` — an immutable-style substitution/binding environment used during matching and quantifier handling (`bind`, `walk`, `occurs`, blocked-variable tracking).
- `KnowledgeBase` (`KnowledgeBase` class, `kb` throughout the code) — the central mutable-ish context: current theory (proven formulas), symbol table (fixity/arity/aliases/bool signatures), and a **level stack**. Proof blocks (`proof`, `assume`, `case`, `let`, `pick`) push/pop levels via `push_level` / `pop_level` / `merge_and_pop`, each level scoping its own local assumptions and constants that get discharged when the block closes (e.g. `assume`/`case` blocks introduce a hypothesis that must be resolved before merging back into the parent level).

Loading and modularity:

- `load_file` resolves `load "foo.kurt"` against `theory_path` (cwd first, then the packaged `kurt.theories` resources) — this is how `.kurt` files pull in reusable theories (see `src/kurt/theories/*.kurt`: `minimal.kurt`, `prop.kurt`, `logic.kurt`, `equality.kurt`, `arith.kurt`, `set.kurt`, `natural.kurt`, `induction.kurt`, `modal.kurt`, `lambda-calculus.kurt`, `latex.kurt`).
- `initial_kb` (module-level) is the pristine starting `KnowledgeBase`; tests `copy.deepcopy` it per test case to avoid cross-test contamination.
- `mainstream` (a bool threaded through most eval functions) distinguishes output that should be printed/logged from output produced while silently loading dependencies.

Docs worth reading before non-trivial language changes: `doc/kurt-doc.md` (language reference, describes current behavior only), `doc/kurt-cookbook.md` (task-oriented recipes), `doc/dev-notes.md` (chronological design-decision diary, not a reference — history of *why*, not a description of *what is*), `tutorial/*.kurt` and `tutorial/plan.md` (hands-on lessons). `todo.md` tracks known-missing features and open design questions; `todo-claude.md` and `suggestions-claude.md` are a filtered/verified pass over that backlog plus independent implementation-improvement ideas — check these before assuming something is a bug rather than a documented gap.
