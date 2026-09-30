# Codex review and implementation suggestions

Date: 2026-09-29

## Scope of this review

This review covered the repository structure, project and release documentation, all shipped
theories, the tutorial and proof corpus, the test harness, CI, supporting scripts, and the full
`src/kurt/kurt.py` implementation. Existing `dev/todo.md`, `dev/todo-claude.md`, and
`dev/suggestions-claude.md` were treated as prior work; the recommendations below either add a new
finding or turn an important existing idea into a concrete implementation brief.

Verification performed on this checkout:

- Branch: `agent-codex`.
- `PYTHONPATH=src python3 -m unittest`: 136 tests passed.
- `python3 scripts/line_coverage.py`: 4519/4906 executable lines, 92.1%.
- `python3 -m compileall -q src tests scripts`: passed.
- The standalone builder and its smoke tests are exercised by both the test suite and CI.

## Overall assessment

Kurt has a strong and coherent goal: a dependency-free proof language that is close to ordinary
written mathematics, gives line-by-line feedback, and can be distributed to students as one
Python file. The code supports that goal well. Particularly strong points are:

- The language grammar and most inference rules are visible in `.kurt` theory files rather than
  hidden in Python.
- Exact `Fraction` arithmetic avoids floating-point proof surprises.
- The adversarial `proofs/soundness/` corpus records real historical failures, not only happy
  paths.
- Every accepted proof step has a certificate that is checked again by `kernel_verify`.
- `.kurtc` files are hints rather than trusted proof state.
- The project has no runtime dependencies, broad Python-version CI, a real standalone bundle,
  and unusually high coverage for a language implementation at this stage.

The main weakness is no longer a lack of features. It is that several logically separate
concerns still share mutable state, representations, and helper functions. `kurt.py` is about
6,800 lines and contains the lexer, parser, session state, proof search, certificate persistence,
kernel, file loader, REPL, and CLI. This is manageable today because the comments and regression
tests are good, but it raises the cost of deciding whether a change affects only search,
user-facing behavior, or the trusted checker.

The recommendations are ordered for the path to a public 0.9 and a trustworthy 1.0. They do not
recommend abandoning the single-file classroom artifact or adding runtime dependencies.

## Priority summary

| Priority | Work package | Why it matters |
|---|---|---|
| P0 | Replace reflective load/export merging with an explicit export transaction | Removes a fragile, soundness-adjacent state boundary |
| P0 | Check each loaded theory in an isolated context | Makes theory validity independent of load order and improves performance predictability |
| P0 for 1.0 | Reduce and freeze the kernel's trusted computing base | Makes the certificate claim precise and auditable |
| P1 | Introduce an explicit per-run context and small public API | Enables reliable browser, editor, grader, and concurrent use |
| P1 | Add indexed proof search with performance regression cases | Preserves immediate classroom feedback as theories grow |
| P1 | Turn diagnostics into structured events | Supports teaching, grading, the browser, and better explanations without duplicating the checker |
| P2 | Fix three confirmed small defects and stale documentation | Low-risk correctness and polish wins |

## P0: replace reflective load/export merging with an explicit export transaction

### Problem

`KnowledgeBase.merge_and_pop` currently filters the child, then loops over
`self.__dict__` and decides how to merge each attribute by testing whether the parent value has
`update` or `extend`. Correctness therefore depends on an exclusion set staying synchronized
with every field added to `KnowledgeBase`.

There is already evidence of how easy this is to get wrong: the exclusion set contains
`"mode_expr"`, but the real field is `mode_args`. This is harmless for today's implicit load
boundary because its arguments are empty, but the mechanism makes future fields export by
default. A new list, set, or dictionary added for session bookkeeping could silently leak from a
loaded file into its caller.

This method is part of the boundary that decides what a theory exports. It should fail closed:
new fields should remain local unless code explicitly exports them.

### Suggested implementation

1. Add a small `ExportBundle` dataclass whose fields are exactly the state allowed to cross a
   file boundary: exported formulas, required symbol declarations, calculator bindings, and any
   load metadata that intentionally survives.
2. Split `merge_and_pop` into pure, separately testable operations:
   - `compute_exports(child) -> ExportBundle`
   - `validate_exports(bundle, child, parent)`
   - `apply_exports(parent, bundle)`
3. Copy mutable collections into the bundle. Do not let parent and child share dictionaries or
   lists accidentally.
4. Keep the existing selective-export rules: only labelled non-`local` formulas, only symbols
   reachable from those formulas, aliases to a fixed point, and rejection of exported facts that
   depend on a local definition.
5. Delete the `__dict__` loop and the exclusion set after parity tests pass.

### Acceptance tests

- Parameterize tests over every exportable syntax property (`infix`, `prefix`, `postfix`,
  `brackets`, `arity`, `bindop`, `flat`, `sym`, `alias`, `bool`, and `calc`).
- Verify that each required property crosses the boundary and each unused property does not.
- Add a dummy non-export field to a child in a unit test and prove it cannot reach the parent.
- Retain all existing `load-export-*`, frozen-operator, and arity-conflict regressions.
- Loading the same theory twice must remain idempotent.

## P0: check loaded theories in an isolated context

### Problem

`load_file` checks a library using the caller's current `KnowledgeBase`. A library can therefore
accidentally rely on a fact or declaration that its caller loaded earlier but that the library
did not declare as a dependency. Its correctness and runtime can change with load order. This is
already noted in `dev/todo.md`; it should be elevated because it affects reproducibility, modularity,
and the meaning of a successful check.

### Suggested implementation

1. Canonicalize the requested path and construct a fresh file-checking context containing only:
   - the immutable Kurt core,
   - the current run configuration (`strict`, trusted paths, output policy), and
   - exports of dependencies explicitly loaded by this file.
2. Check the file completely in that context.
3. Produce an `ExportBundle` as described above and merge only that bundle into the caller.
4. Cache a checked bundle by canonical path, source hash, Kurt fingerprint, and dependency
   hashes. The cache remains an optimization; reconstruct and validate the bundle before use in
   the same spirit as `.kurtc`.
5. Keep relative-load resolution relative to the loading file, and keep the existing cycle
   detection based on canonical paths.

### Acceptance tests

- A helper that uses a fact from its caller without `load`ing the defining theory must fail.
- The same helper must pass after adding its explicit dependency.
- Permuting independent top-level `load` statements must not change success, exported formulas,
  or certificates.
- Loading a library after a large unrelated theory must not enlarge the facts visible while the
  library itself is checked.
- Existing diamond-load, relative-load, duplicate-load, cycle, `.kurtc`, and selective-export
  tests must keep passing.

## P0 for 1.0: reduce and freeze the kernel's trusted computing base

### Problem

The certificate kernel is the most important architectural improvement in the repository. It is
not yet a tiny independent checker, however. As documented in `doc/kurt-soundness.md`, it still
trusts the parser, `unpack_condition`, `normalize_expr`, and `equal_expr`; normalization in turn
depends on the mutable syntax tables in `KnowledgeBase`. Search and verification therefore share
some of the code most likely to contain a subtle binding, alpha-equivalence, `flat`, `sym`, or
calculator bug.

The release plan still contains older statements that "the whole matcher is trusted" and "all of
it" is trusted. Those are no longer accurate, but simply replacing the prose with "small kernel"
would also overstate the current separation.

### Suggested implementation

Use a staged reduction rather than a risky rewrite:

1. Write down a machine-checkable kernel dependency list. A lightweight AST-based test can reject
   new calls from `kernel_verify*` and `k_*` functions into search-only helpers.
2. Give the kernel an immutable `KernelEnvironment` snapshot containing only symbol arities,
   binder declarations, boolean signatures, flat/symmetric declarations, and calculator bindings
   needed for the certificate being checked.
3. Implement kernel-local alpha-equivalence and binder decoding. These should not call
   `equal_expr` or `unpack_condition` from proof search.
4. Decide explicitly how much normalization is part of the logic. For each of `flat`, `sym`, and
   `calc`, either:
   - encode the normalization step in the certificate and check it with a small kernel rule, or
   - keep it in the kernel environment and name it as trusted semantics.
5. Keep certificate mutation tests, but also add property tests that generate small typed terms
   and compare search acceptance with kernel acceptance. No third-party property-testing library
   is required; a deterministic bounded generator is sufficient.
6. Do not split files merely for appearance. The source may remain in one file until the trust
   boundary is genuinely cleaner. If development modules are introduced later, extend
   `build_standalone.py` to produce the same single-file classroom artifact.

### Acceptance criteria

- `doc/kurt-soundness.md` names every trusted component and why it is trusted.
- A CI test prevents accidental calls from kernel code to proof-search substitution or matching.
- The kernel environment is immutable for the duration of one verification.
- The existing forged-certificate tests and all adversarial proof files pass.
- The release plan describes the actual trust boundary rather than both the pre-kernel and
  post-kernel architectures at once.

## P1: introduce an explicit per-run context and small public API

### Problem

State for one check is spread across `KnowledgeBase` and mutable module globals, including
`strict_mode`, `trusted_paths`, `theory_path`, `new_symbols`, `accepted_lines`, `origin_names`,
`dependent_vars`, `certificates_by_line`, `current_line`, `replay_hints`, `load_dependencies`,
`_loading_in_progress`, the fresh-name counters, and one-element lists used as mutable boxes.

This is mostly harmless for a one-shot CLI, but it is a poor fit for the project's stated browser,
editor, and autograder goals. Two checks in one Python process can influence generated names,
diagnostics, caches, or configuration unless every caller knows which globals to reset. Parallel
checks are not safe.

### Suggested implementation

1. Add `RunConfig` for immutable options and `RunContext` for per-run mutable state.
2. Move counters, current source location, accepted lines, certificate collections, dependency
   tracking, load-cycle state, and replay hints into `RunContext`.
3. Pass the context through `load_file` and the evaluator, or attach it to the root
   `KnowledgeBase` and retrieve it from child levels. Avoid another module-global singleton.
4. Provide a deliberately small supported API:
   - `new_session(config: RunConfig | None = None) -> Session`
   - `check_text(text, *, name="<memory>", session=None) -> CheckResult`
   - `check_file(path, *, session=None) -> CheckResult`
5. Let the existing CLI be a thin adapter over this API. Keep current stdout text as the default
   renderer for compatibility.
6. Replace `from .kurt import *` in `src/kurt/__init__.py` with an explicit `__all__` for the
   supported API. Tests that need internals can continue importing `kurt.kurt`.

### Acceptance tests

- Two sessions checking the same text produce identical generated names and certificates.
- Strict mode, trusted paths, `calc`, accepted lines, and failed loads do not leak between runs.
- Interleaving two sessions in one process gives the same result as running them separately.
- Existing CLI output and exit-code tests remain byte-for-byte compatible unless a change is
  explicitly documented.

## P1: index proof search and add performance regression cases

### Problem

`derive_expr` and `match_all_theory` scan all formulas. Matching flat and symmetric operators can
enumerate set partitions and then permutations. This is understandable and works for the current
small corpus, but runtime will become unpredictable as theory libraries and student contexts
grow. Immediate feedback is part of Kurt's teaching value, so performance failures are usability
failures.

### Suggested implementation

1. Add a benchmark script with representative cases before changing the algorithm:
   - a large irrelevant theory plus a simple goal,
   - a long conjunction matched against two- and three-variable schemas,
   - nested `sub` matching,
   - the current `group.kurt` after unrelated theories are loaded.
2. Maintain indexes when formulas are appended:
   - facts by top-level operator,
   - implications by the top-level operator of their conclusion,
   - a fallback bucket for variable-headed or otherwise non-indexable conclusions.
3. Preserve theory order within each bucket so the selected proof and printed reason do not
   change merely because indexing was added.
4. Use cheap shape and type filters before `partitions`/`permutations`. Memoize failed
   `(expression shape, pattern shape, relevant substitution)` states within one derivation only.
5. Add generous CI thresholds or relative benchmarks that catch order-of-magnitude regressions
   without becoming timing-flaky.

### Acceptance criteria

- All existing certificates and human-readable reasons remain stable on the proof corpus.
- An irrelevant theory increases lookup cost sublinearly after indexing.
- The benchmark includes at least one case that would be combinatorial without pruning.
- Complexity comments live beside the relevant branch in `unify_exprs_with_patterns`.

## P1: emit structured diagnostics, then render text

This develops the existing JSON-report/output-renderer idea into one design rather than adding a
second reporting path.

1. Define events such as `FormulaAccepted`, `BlockOpened`, `BlockClosed`, `Warning`,
   `ProofFailed`, `CertificateChecked`, and `FileLoaded`.
2. Make evaluator code emit events into `RunContext`; do not parse current reason strings later.
3. Reimplement today's terminal output as a renderer over those events and lock compatibility
   with golden tests.
4. Add a JSON renderer for graders and a compact object result for Pyodide/editor consumers.
5. Build `why`/`hint` features from certificates and structured events, not from additional proof
   search. A failed derivation may report the closest candidate rules and which premises were
   missing, with a strict cap on search performed for diagnostics.

This work directly serves the classroom, browser, and autograder goals while simplifying the
`mainstream`, filename, `decorate_reason`, and direct-`print` plumbing.

## P2: confirmed small fixes

These are suitable for separate, reviewable commits before larger refactors.

### 1. Fix the `parse` type-error branch

In `parse_tokenstream`, the exception handler tests:

```python
if keyword_token in ['parse']:
```

`keyword_token` is a `Token`, so this condition is always false. Test
`keyword_token.value == 'parse'` (after the existing `None` guard) instead. Add a unit test where
`parse` receives a syntactically valid but ill-typed expression and assert that the intended
`type check failed` diagnostic is printed rather than the ordinary `parsed as` diagnostic.

### 2. Fix multi-definition logging

The `def` branch first loops over `args` with `for expr in args`, then later loops over
`zip(formulas, lhs_consts)` but logs `expr_str(expr, kb)`. At that point `expr` is the final
argument from the earlier loop, so a comma-separated line containing multiple definitions logs
the last definition for every entry.

Store `(formula, lhs_const, original_expr)` together and log the matching expression. Test two
definitions on one line under `mainstream=True` and assert that each printed entry contains its
own expression.

### 3. Restore or deliberately remove REPL history loading

`main()` contains:

```python
if os.path.exists(readline_history_file) and False:
```

This permanently disables reading history while still writing it at exit. If the feature is
desired, remove `and False` and catch `OSError` rather than only `PermissionError`. If history is
not desired, remove both read and write behavior and the dead code. Do not leave a hidden boolean
switch in production code.

## P2: release and documentation consistency

Before public 0.9, make one pass whose only job is reconciling claims with the current tree:

- `CLAUDE.md` says `kurt.py` is about 4,300 lines; it is about 6,800.
- `dev/release-plan.md` says about 5,600 lines and 105 tests; the current suite runs 136 tests.
- The release plan simultaneously says the whole matcher/all code is trusted and says that a
  certificate kernel checks every step. Replace this with the exact trust boundary from
  `doc/kurt-soundness.md`.
- The opening comment in `set.kurt` says mappings include function extensionality, while the
  implementation later correctly and explicitly says function extensionality is not provided.
- `doc/kurt-cookbook.md` is still a stub even though public polish and teaching are primary goals.
  Start with recipes already demonstrated by the corpus: implication proofs, contradiction,
  conditioned quantifiers, equality rewriting, induction, local exports, `calc`, and diagnosing a
  failed step.
- Decide whether the empty repository-root `kurt` file should be removed or replaced by an actual
  launcher. Add `src/kurt/__main__.py` so `python -m kurt` works consistently after installation.
- Build an sdist and wheel in CI, install each into a clean environment, and run a small proof.
  This tests the artifact users receive, not only an editable checkout.

Avoid maintaining numeric code/test counts in several documents if they do not serve a release
requirement. When a count is useful, generate it in a release script or label it with a date.

## Changes I would not make yet

- Do not add more automatic multi-hop inference until soundness boundaries, load isolation, and
  performance budgets are settled. More search would magnify all three risks.
- Do not replace exact arithmetic with NumPy or another approximate/runtime dependency.
- Do not abandon the single-file distribution goal. If development sources are split later,
  treat `dist/kurt.py` as a generated, equivalence-tested artifact.
- Do not perform a wholesale AST rewrite at the same time as kernel changes. First make run state
  and export behavior explicit; then an immutable expression representation can be evaluated as
  a separate migration with round-trip and certificate tests.

## Recommended execution order

1. Land the three confirmed small fixes with regression tests.
2. Replace reflective export merging with `ExportBundle`.
3. Implement isolated file checking on top of that explicit bundle.
4. Introduce `RunContext` and the small public API without changing CLI output.
5. Add benchmarks and theory indexes.
6. Tighten the kernel boundary in staged commits, updating the soundness document with each
   reduction in trusted code.
7. Build structured diagnostics and the first real cookbook recipes before public 0.9.

This order keeps behavioral changes small, makes later work easier to test, and protects Kurt's
most distinctive strengths: readable proof files, immediate feedback, no runtime dependencies,
and a one-file classroom distribution.
