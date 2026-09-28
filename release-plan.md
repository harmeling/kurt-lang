# Release and publication plan

(started 2026-09-28)

## Where Kurt stands

Already there:

- one-file implementation (`src/kurt/kurt.py`, ~5600 lines), MIT license, installs with `pip`
- CI green on Python 3.10, 3.12, 3.13 (it had been failing since e5a97db, fixed in 81f6ada)
- 105 tests, about 92.5% line coverage (`scripts/line_coverage.py`)
- documentation: language reference (`doc/kurt-doc.md`), soundness audit (`doc/kurt-soundness.md`),
  46 tutorial lessons
- theories: prop, logic, equality, set, arith, natural, analysis, modal

## What stands between Kurt and 1.0

1. **Freeze the language.** 1.0 promises that proofs written today keep working. Open design
   questions that would break existing proofs -- decide each: before 1.0, or never:
   - [ ] minimal core, quantifiers only with `load logic` (todo.md)
   - [ ] `f(a,b)` meaning `f a b` (todo.md)
   - [ ] labels: keep, or "the first word of the comment" (todo.md)
   - [ ] `save` as a replay of the input
   - [ ] `use` only directly in `sandbox`/`expect`
   - [ ] `ParseError` vs. `EvalError` for wrong arguments (currently mixed)
2. **Confidence in soundness.** The promise of a checker is "what Kurt accepts is correct". In
   September 2026 several soundness bugs were found and fixed (forall-elim proving any two things
   equal, a rule variable depending on a forall premise's variable, Russell's paradox in
   set.kurt) -- that rate says the engine isn't settled. Reviewers will note that Kurt has no
   small trusted kernel (LCF style): the whole matcher is trusted; `doc/kurt-soundness.md` is the
   answer so far.
   - [ ] a period of adversarial testing, e.g. students get credit for breaking it
3. **Real use.**
   - [ ] one semester in a course (mafi1), collect what students trip over -- also the evidence
     for an education paper
4. **Public polish.**
   - [ ] README: longer, current version, installation, a gallery of example proofs
   - [ ] `doc/kurt-cookbook.md` is a stub
   - [ ] sort out the internal files in the repo root: `CLAUDE.md`, `todo-claude.md`,
     `suggestions-claude.md`, `notes-on-*.md`, `lab-notes.md`, `llms.txt`, the empty file `kurt`
     (note: the git history contains everything)
   - [ ] version number (`pyproject.toml` and the banner say 0.1)
   - [ ] make the repository public

Suggestion: go public now as **0.9** (a 0.x version says "not stable yet") and put it on PyPI;
call it 1.0 after the language freeze and a semester of use.

## Other ways to publish

- **Citable releases**: PyPI (`pip install kurt-lang`, check that the name is free), Zenodo (a DOI
  for each GitHub release)
- **In the browser**: Kurt via Pyodide on GitHub Pages (todo.md) -- students install nothing; for a
  teaching tool probably the most important item here
- **Online book**: the tutorial lessons plus exercises, as a Jupyter Book or mdBook with runnable
  Kurt. Models: Avigad et al., *Logic and Proof*; Lean's *Natural Number Game*
- **Papers** (check the actual deadlines):
  - ThEdu (Theorem Proving Components for Educational Software), workshop, proceedings in EPTCS --
    the best fit for a system description
  - CICM (Conferences on Intelligent Computer Mathematics), system-description track
  - ITP / IJCAR / CADE system descriptions -- higher bar, needs a careful comparison
  - JOSS (Journal of Open Source Software) -- short, reviewed, citable; needs a public repo,
    documentation, tests, and a statement of need
  - education research, with an evaluation with students: SIGCSE, ITiCSE, Koli Calling, ACM
    TOCE; in German: DELFI, HDI
- **Related work** reviewers will ask about: Diproche and Naproche (Koepke et al., controlled
  natural language), Waterproof (Eindhoven, Coq for teaching), Lurch, Mizar, Isabelle/Isar.
  Kurt's points: one file, no dependencies, the grammar itself declared in Kurt's theory files,
  immediate feedback for each line.

## Order

1. [ ] public 0.9, PyPI, Zenodo
2. [ ] browser version, online book
3. [ ] ThEdu paper, JOSS
4. [ ] course semester, then an education paper
