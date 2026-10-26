# Exercises

Exercises for students, by topic. Each topic is a folder: its exercises are the `.kurt` files in
it, and its *scene* is in `theory/` -- a theory that the exercises load, which declares what the
topic talks about (the symbols, how to write them) and the rules that hold there. The scene keeps
an exercise small: the exercise only states what is to be proven.

## Working on an exercise

Open the exercise, e.g. `01-knights-and-knaves/2-two-islanders.kurt`, and read it: its comments
pose the questions (often in parts (a), (b), ...), and the scene in `theory/` says what you may
use. Each statement to prove is a `show` line followed by a proof that is still a `todo`:

    show (A says knave(A) ∧ knave(B)) ⇒ knave(A) ∧ knight(B)
    proof
        todo
    qed

Replace the `todo` by your proof, and check the file:

    cd exercises/01-knights-and-knaves
    kurt 2-two-islanders.kurt

(`kurt` is the command after `pip install -e .`, see the README; without it, `python -m kurt
2-two-islanders.kurt` from the repository.)

Kurt checks each line and says why it follows, or where it gets stuck. As long as `todo`s are
left, it ends with `Proof almost checked: N todos.`; when every part is proven, with `Proof
checked`. Don't change the `show` lines or the scene, and don't add axioms (`use`): your proof
must follow from the scene. You may add lemmas of your own (`show ... proof ... qed`) before a
part that needs them.

**In the browser**, without installing Kurt: the playground ([www.kurt-lang.org](https://www.kurt-lang.org))
has the exercises in its menu "exercises", and a link opens one directly, e.g.
[`www.kurt-lang.org/#file=exercises/01-knights-and-knaves/2-two-islanders.kurt`](https://www.kurt-lang.org/#file=exercises/01-knights-and-knaves/2-two-islanders.kurt)
-- a link a teacher can hand out. The playground keeps your text in the browser (download it
with File, for grading).

New to Kurt? The tutorial (`../tutorial/`, one task per lesson) shows how to prove an implication
(`assume`), a negation (by contradiction), a `∀` (`let`), how to use a `∃` (`pick`), and how to
split into cases (`case`).

## Grading

    python3 scripts/grade_exercise.py exercises/01-knights-and-knaves/2-two-islanders.kurt submission.kurt

checks the submission as `kurt --strict --all-errors` would (no `use`, `todo` or `chain`; every
symbol declared; an error doesn't stop the check), next to a copy of the exercise's `theory/`,
which it trusts (as with `-p`). Then it looks up each `show` of the exercise in the submission --
as Kurt reads it, so `A ⇒ B` and `A implies B` are the same statement, and the order doesn't
matter; with the exercise's label, if it has one -- and says how it stands: `proved` (a proof
that rests on no `todo` and no error), `admitted` (a `todo` in its proof, or an error), `assumed`
(`use`), `loaded` (from a file, not proved here) or `missing` (not there, changed, or withdrawn
with `break`). The submission may add lemmas of its own, but may load only what the exercise
loads (directly or through the scene): a file that states an answer is no proof. The report:

    checked (strict)
    proved: (A says S) ∧ knight(A) ⇒ S
    admitted: (A says S) ∧ knave(A) ⇒ ¬S
    missing: ¬(A says knave(A))
    NOT COMPLETE

`COMPLETE` (exit code 0) needs a check without errors, every statement proved and nothing else
loaded; otherwise `NOT COMPLETE` (exit code 1). Use the teacher's copy of the exercise, not the
student's. From Python, the same questions are `CheckResult.proves(statement, label)`,
`proof_of` and `loaded` (doc/kurt-ref.md §1).

## Topics

| folder | topic | the scene |
|---|---|---|
| `01-knights-and-knaves/` | propositional logic: puzzles about islanders who always tell the truth or always lie | `theory/island.kurt` |
| `02-family-tree/` | predicate logic: ∀ and ∃ with parents, grandparents, siblings; negating quantifiers | `theory/family.kurt` |
| `03-sets/` | set algebra: subsets, equal sets, the complement and De Morgan | `theory/sets.kurt` |
| `04-functions/` | maps between sets: injective, surjective, composition, image, preimage | `theory/maps.kurt` |
| `05-relations/` | relations: equivalence relations and classes, partial and strict orders | `theory/relations.kurt` |
| `06-groups/` | groups from weak axioms: right inverse and neutral element, uniqueness, equations, subgroups | `theory/groups-scene.kurt` |
| `07-induction/` | induction: Peano arithmetic from scratch; sums and powers | `theory/peano.kurt`, `theory/recursion.kurt` |
| `08-limits/` | limits of sequences with ε and N: first limits, limit laws, uniqueness | `theory/limits.kurt` |
| `09-calculus/` | derivatives and integrals: the rules, ε-δ, the fundamental theorem | `theory/calculus.kurt`, `theory/definitions.kurt` |

## Writing an exercise

- A topic folder `NN-name/` with its scene in `NN-name/theory/`. The scene loads the theories of
  Kurt it needs, declares the topic's symbols (with a header that lists them and the rules, by
  their labels), and states the rules with `use` or `def`. Prove in the scene what follows from
  its rules and is only a tool, not an exercise (e.g. "knight" in island.kurt).
- An exercise `N-name.kurt` loads its scene (`load theory/NAME`), declares its constants, and
  states each part as a `show` with a proof that is `todo`. Its premises are the left side of the
  statement (`show P ∧ Q ⇒ R`), not axioms: a student's file under `--strict` can't have `use`.
  The comments pose the question, and give hints where a first step is not obvious.
- Each exercise has a solution: the same file with the `todo`s replaced. The solutions are not
  published, so that the exercises can be used in a course; teachers can ask the author for
  them. `tests/test_exercises.py` checks the scenes, checks that each exercise runs with its
  `todo`s, and grades each solution with `scripts/grade_exercise.py` (where the solutions are
  present).
