# Release and publication plan

(started 2026-09-28)

## Where Kurt stands

Already there:

- one-file implementation (`src/kurt/kurt.py`), MIT license, installs with `pip`
- CI green on Python 3.10, 3.12, 3.13 (it had been failing since e5a97db, fixed in 81f6ada)
- on 2026-09-29: 161 tests, about 92% line coverage (`scripts/line_coverage.py`); the numbers
  change with every commit, `python -m unittest` and the coverage script give the current ones
- documentation: language reference (`doc/kurt-doc.md`), soundness audit (`doc/kurt-soundness.md`),
  46 tutorial lessons
- theories: prop, logic, equality, set, arith, natural, analysis, group, modal

## What stands between Kurt and 1.0

1. **Freeze the language.** 1.0 promises that proofs written today keep working. Open design
   questions that would break existing proofs -- decide each: before 1.0, or never:
   - [ ] minimal core, quantifiers only with `load logic` (dev/todo.md)
   - [ ] `f(a,b)` meaning `f a b` (dev/todo.md)
   - [ ] labels: keep, or "the first word of the comment" (dev/todo.md)
   - [ ] `save` as a replay of the input
   - [ ] `use` only directly in `sandbox`/`expect`
   - [ ] `ParseError` vs. `EvalError` for wrong arguments (currently mixed)
2. **Confidence in soundness.** The promise of a checker is "what Kurt accepts is correct". In
   September 2026 several soundness bugs were found and fixed (forall-elim proving any two things
   equal, a rule variable depending on a forall premise's variable, Russell's paradox in
   set.kurt) -- that rate says the engine isn't settled. Since then, every step the search
   accepts is checked again by a kernel (`kernel_verify`) -- but not a small one yet: it still
   trusts the parser, `unpack_condition`, `normalize_expr` (`flat`, `sym`, `calc`) and
   `equal_expr`, which it shares with the search (`doc/kurt-soundness.md` §9 names them; making
   the kernel independent of them is in dev/todo.md, from dev/codex-suggestions.md).
   - [ ] a period of adversarial testing, e.g. students get credit for breaking it
   - [x] a small checking kernel: certificates for each step, checked by `kernel_verify`, on in
     the test suite (`doc/kurt-soundness.md` §9)
   - [x] the kernel also for closing blocks and `pick`
   - [ ] decide when a schema variable may depend on a bound variable (implicit as now,
     declared like Isabelle's `?T i`, or Metamath-style distinct-variable conditions)
3. **Real use.**
   - [ ] one semester in a course (mafi1), collect what students trip over -- also the evidence
     for an education paper
4. **Public polish.**
   - [ ] README: longer, current version, installation, a gallery of example proofs
   - [x] `doc/kurt-cookbook.md`: 20 recipes (by Codex, 2026-09-29)
   - [ ] sort out the internal files in the repo root: `CLAUDE.md`, `dev/todo-claude.md`,
     `dev/suggestions-claude.md`, `notes-on-*.md`, `dev/lab-notes.md`, `llms.txt`, the empty file `kurt`
     (note: the git history contains everything)
   - [ ] version number (`pyproject.toml` and the banner say 0.1)
   - [ ] make the repository public

Suggestion: go public now as **0.9** (a 0.x version says "not stable yet") and put it on PyPI;
call it 1.0 after the language freeze and a semester of use.

## Other ways to publish

- **Citable releases**: PyPI (`pip install kurt-lang`, check that the name is free), Zenodo (a DOI
  for each GitHub release)
- **In the browser**: Kurt via Pyodide on GitHub Pages (dev/todo.md) -- students install nothing; for a
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

## Kurt compared with other proof languages (for the paper)

"Simple" can mean three things: what you have to learn before your first proof, what the
language rests on, and what you have to trust. (Figures for other systems are rough, to be
checked.)

| | first proof needs | logical foundation | proof style | implementation / what you trust |
|---|---|---|---|---|
| **Kurt** | `bool A, B`, `use`, one line per step; 43 keywords in total | untyped first-order logic, only "boolean or not"; rules are ordinary `use` lines | a sequence of claims, each checked automatically in one step | one Python file, no dependencies; a kernel checks each step, but shares the parser, normal forms and alpha-equivalence with the search |
| **Metamath** | substitution rules, labels, very low-level steps | none built in: axioms plus substitution | every rewriting step spelled out | tiny checker (a few hundred lines) and **tiny trusted core**, but hard to read |
| **Mizar** | a large library, its own vocabulary | Tarski–Grothendieck set theory, soft types | declarative, readable | large system; library and checker trusted |
| **Isabelle/Isar** | HOL, types, Isar structure, many tools | higher-order logic | declarative (Isar) or tactics | very large; small LCF kernel |
| **Lean 4 / Coq** | dependent types, tactics, a library (Mathlib) | dependent type theory | mostly tactics | very large; relatively small kernel |
| **Naproche / Diproche** | controlled natural language | first-order logic plus an automatic prover (Naproche) | text close to mathematical prose | medium; the automatic prover is also trusted |
| **Waterproof** | Coq underneath, controlled language on top | as Coq | text-like tactics | Coq plus a layer on top |

Where Kurt is simpler:

- **Getting started**: no types, no tactics, no library to learn; a first proof is five lines,
  and each line gets its own feedback. Only Metamath comes close in concepts, and its proofs are
  much harder to read.
- **The logic is visible**: even the grammar (`infix`, `bindop`, `chain`) and the rules
  ("forall-elim", "lim-intro") are Kurt text in theory files -- students can read why a step goes
  through; in Lean or Isabelle a lot of this is hidden in tactics and automation.
- **Deployment**: one file to copy into a classroom; the others need an installation, and often
  a large library.

Where Kurt is *not* simpler (reviewers will say so):

- **What you trust**: Metamath, HOL Light and Isabelle have small kernels that check everything
  else. Kurt's kernel checks every step of the search (unification, `sub` matching, calc,
  chains) again, but it is not small yet: it shares the parser, the normal forms (`flat`, `sym`,
  `calc`) and alpha-equivalence with the search, and the block rules and `load` are checked by
  ordinary code (`doc/kurt-soundness.md` §9). Kurt's simplicity is on the user's side, not yet
  fully on the side of trust.
- **What happens inside a step is hard to predict**: Kurt searches for a single step itself,
  with second-order matching for `sub`. Convenient, but when a step fails it is hard to say why
  (the `calc off` workarounds, "forall-cond-def" after `let x ∈ A`).
- **Expressiveness**: without types, functions on the reals are untyped symbols (`abs`, `lim`),
  with care about their values where nothing is defined (the intro-only rules of analysis.kurt);
  typed systems catch such mistakes automatically.

In one sentence: Kurt is at the simple end for *writing and reading* proofs -- about as simple as
Metamath in concepts, but readable like Mizar or Isar -- but not yet for *trust*. A small checking
kernel would be the most valuable step toward 1.0 (and a strong point for the paper).

## Order

1. [ ] public 0.9, PyPI, Zenodo
2. [ ] browser version, online book
3. [ ] ThEdu paper, JOSS
4. [ ] course semester, then an education paper
