# Kurt

<img src="https://raw.githubusercontent.com/harmeling/kurt-syntax/main/images/logo.svg" alt="the logo of Kurt: ⊢kurt" width="96" align="right">

Kurt is a programming language for writing mathematical proofs in a form close to how people write
them — one claim per line, blocks for assumptions and cases — and a checker that tells you
immediately, line by line, whether each step follows. It is meant for students learning to prove
things, much like running tests while learning to program. Kurt has been developed by Stefan
Harmeling (TU Dortmund) since 2016.

**Status: 0.10, a public beta.** Kurt is used for teaching, but the language isn't frozen yet: a
proof written for 0.10 may need small changes for 1.0 (for 0.9 to 0.10: the "breaking changes" in
`CHANGELOG.md`).

**Try it in your browser**, without installing anything:
[www.kurt-lang.org](https://www.kurt-lang.org), the playground. It runs the same Kurt in the
browser, with the tutorial, the keyword lessons, the exercises, and the proofs of a lecture
(mafi1). A link can open one of these files, e.g. for a course:
[`www.kurt-lang.org/#file=exercises/01-knights-and-knaves/2-two-islanders.kurt`](https://www.kurt-lang.org/#file=exercises/01-knights-and-knaves/2-two-islanders.kurt)
(`#file=` and the file's path in the playground; see `doc/kurt-doc.md`, §1).

## A first proof

A file `modus-ponens.kurt`:

    ; simple modus ponens proof
    prop A, B
    use A implies B
    use A
    B

Check it on the command line:

    $ kurt modus-ponens.kurt
    This is Kurt, v0.10.0 (made by Stefan Harmeling, 2016-2026), 6cc39e5bab2c (SHA-256 of kurt.py)
       3  use A implies B                           ; without proof
          const A                                   ; added constant
          const B                                   ; added constant
       4  use A                                     ; without proof
       5  B                                         ; by 3(4)
    Proof checked

Each line gets the reason it holds: `B` follows by the rule of line 3 from the fact of line 4.
A proof with blocks, from the theory `propositional` that comes with Kurt:

    ; if A implies B, then not B implies not A
    load propositional
    prop A, B

    show (A implies B) implies (not B implies not A)
    proof
        assume A implies B
            assume not B
                assume A
                    B
                    false
                not A
    qed

`kurt` without a file starts an interactive shell, which reads the same language, with the
same indentation rules as a file.

## What Kurt offers

- **Proofs as text**, line by line. Kurt finds each single step by itself, from the facts and
  rules around. You don't need tactics or rule names.
- **Theories written in Kurt itself**: propositional and first-order logic, equality, sets,
  arithmetic, natural numbers with induction, analysis (sums, limits, derivatives, integrals), groups, and modal logic
  T (with `⊢ A` for "A is a theorem", modus ponens and necessitation).
  Even the grammar is declared there (`infix`, `bindop`, `chain`), so students can read why a
  step goes through.
- **A kernel checks every step again**: the search hands each accepted step to a small checker
  as a certificate. `cert N` shows the certificate of line `N`. The certificates of a checked
  file are kept in a `.kurtc` file, and next time the kernel checks them again, without any
  search.
- **Exact arithmetic** with `calc on`: `0.1 + 0.2 = 0.3` holds, and `1 / 3` stays a fraction.
- **For grading**: `kurt --strict` rejects axioms (`use`), `todo` and new rules outside the
  theories that come with Kurt.
- **Documents**: `kurt --latex FILE` and `kurt --markdown FILE` write the checked proof with its
  reasons in mathematical notation (`-o OUT` elsewhere, `-o -` to the standard output);
  `kurt --lean FILE` a Lean 4 file (a prototype); `kurt --unused FILE` names the lines of the
  proofs that nothing cites; `kurt --foundation FILE` shows what each theorem rests on (which
  axioms, definitions and `todo`s), for choosing a trusted set of theories.
- **No dependencies**: one Python file. It's also available as a single self-contained script
  with all theories embedded, to hand out in a course.

## Installing

With Python 3.10 or newer, from [PyPI](https://pypi.org/project/kurt-lang/):

    pip install kurt-lang

Then run `kurt` or `python -m kurt`. The newest state of the repository, between releases:
`pip install git+https://github.com/harmeling/kurt-lang.git`.

With [uv](https://docs.astral.sh/uv/), to get the `kurt` command on your PATH without touching
any project environment:

    uv tool install kurt-lang

**Without installing**, for a course: download the single self-contained `kurt.py` of the
latest release,

    https://github.com/harmeling/kurt-lang/releases/latest/download/kurt.py

It has all the theories embedded (`load propositional` and so on work right away) and needs nothing but
Python: `python3 kurt.py proof.kurt`. You can also build it from this repository yourself, with
`python3 scripts/build_standalone.py` (writes `dist/kurt.py`). To keep the theories as separate, editable files instead,
copy `src/kurt/kurt.py` together with the directory `src/kurt/theories/`.

**From Python**, e.g. for a grader or an editor:

    import kurt
    result = kurt.check_text('load propositional\nbool A, B\nuse A implies B\nuse A\nB\n')
    result.ok, result.complete, result.error, result.output     # complete: also no `todo` left
    result.events      # each line: its id, kind, rule, the lines it uses (also `kurt --json FILE`)

    session = kurt.new_session(kurt.RunConfig(strict=True, paths=('teacher/',), time_limit=30))
    session.check_file('proof.kurt')        # time_limit: seconds of search per line (`kurt --budget 30`), else a `ResourceError`

Each session has its own options and state (fresh names, certificates, the cache of checked
theories), so checks in one process don't influence each other -- one check at a time; for checks
in parallel, use processes.

## Documentation

- [`tutorial/`](tutorial/): the tutorial, 30 lessons (00 to 29), task by task: prove an implication, argue by
  contradiction, split into cases, rewrite with equality, use induction, diagnose "can not
  derive". Each one is a Kurt file you can run and change.
- [`keywords/`](keywords/): 48 short lessons (00 to 47), one keyword or idea each
  ([plan](keywords/plan.md)).
- [`exercises/`](exercises/): exercises for students, by topic (logic puzzles, quantifiers, sets,
  functions, relations, groups, induction, limits, calculus): each loads the scene of its topic
  and leaves the proofs to do; `scripts/grade_exercise.py` grades a solution.
- [`doc/kurt-doc.md`](doc/kurt-doc.md): the language reference.
- [`doc/kurt-spec.md`](doc/kurt-spec.md): the logic, specified: variables, the step relation, the
  rules of the blocks, definitions, files, trust, the kernel.
- [`doc/kurt-soundness.md`](doc/kurt-soundness.md): what the checker's correctness rests on,
  rule by rule, and the bugs found so far, each with its regression test.
- [`doc/kurt-kernel.md`](doc/kurt-kernel.md): the kernel step by step, what it checks of each
  step; [`doc/kurt-kernel-code.md`](doc/kurt-kernel-code.md): the same kernel read as code, each
  chunk cited from `kurt.py` and kept the code by a test.
- [`proofs/`](proofs/): many more example proofs. Each one is also a test.

## Why trust it?

A checker is only useful if what it accepts is correct. In Kurt, every step the search finds is
checked again by the kernel. Loaded theories are checked on their own, independent of what was
loaded before. A `def` must be conservative. Adversarial test files (`proofs/soundness/`) keep
every bug found so far from coming back. Kurt is not a small-kernel system like Metamath or HOL
Light yet: the kernel still shares the parser and the normal forms with the search.
`doc/kurt-soundness.md` says exactly what is trusted.

## Proofs people can read

Kurt was made for teaching, and so a Kurt proof is meant to be read by a person: one claim per
line, each with the reason Kurt found for it. That may matter beyond teaching too. As language
models get better at finding proofs, a person still needs to understand what was proven and how;
a checker says that a proof is correct, a readable proof also lets someone follow it. Kurt could
be one way to write such proofs. This is an idea, not a result: Kurt is a small checker, far from
the libraries and the reach of Lean, Isabelle or Coq, and time will tell whether it is useful for
this.

## AI assistance

Stefan Harmeling has designed and developed Kurt since 2016, and AI tools have helped with
parts of the work:

- **ChatGPT**, used in interactive chat to figure out bugs and details of the search procedure,
  in particular how to generate all possible matches.
- **AI coding assistants** since September 2026: Anthropic's Claude via Claude Code, and OpenAI's
  Codex. They implemented features and wrote tests, tutorial lessons and documentation. They
  also reviewed the code for soundness bugs.

The author has not checked every line of the code they produced. He has reviewed the changes,
to see that they do what they should. Every change must also pass the test suite, which checks
every proof in `proofs/` and every tutorial lesson, including the adversarial cases in
`proofs/soundness/`. Commits made with an AI coding assistant say so in a `Co-Authored-By:`
line. The design of the language, and the responsibility for it, remain the author's.

## Editor support

`kurt --lsp` is a language server for editors: the errors and `todo`s at their lines, the reason
of each checked line at its end and on hover (also what a line like `cert 14` or `builtin`
prints), and completion with the state at the cursor. It
checks after open and save, and can check edits after a short debounce; two open files use each
other's unsaved text when one loads the other.

The [kurt-syntax](https://github.com/harmeling/kurt-syntax) repository has editor support for
`.kurt` files: highlighting, comments and indentation, LSP clients for VS Code, Emacs/Eglot and
Neovim, and, in VS Code and Emacs, LaTeX-style shortcuts such as `\forall` → `∀`.

- **VS Code**: the extension **Kurt Proof Language** (`harmeling.kurt-lang`), from the command
  line:

      curl -LO https://github.com/harmeling/kurt-syntax/releases/latest/download/kurt-lang.vsix
      code --install-extension kurt-lang.vsix

  It comes with Kurt itself (only Python 3.10 or newer is needed), and uses an installed `kurt`
  first.
- **Emacs**: put `kurt-mode.el` and `replacements.json` together in a directory on your load
  path, and add `(require 'kurt-mode)` to your configuration.
- **Vim and Neovim**: use the repository as a plugin, e.g. clone it into
  `~/.vim/pack/plugins/start/kurt-syntax`, or into Neovim's plugin directory.

The editor support is new and not completely tested yet (VS Code tried on macOS, Emacs and Neovim
briefly): expect rough edges, and please report what doesn't work. The editors show all errors of
a file (`kurt -a` on the command line; by default it stops at the first).

## Developing Kurt

    python -m venv .venv
    source .venv/bin/activate
    pip install -e .[dev]
    python -m unittest              # the test suite, including every file in proofs/
    coverage run -m unittest && coverage report

The implementation is the single file `src/kurt/kurt.py`. The theories are in
`src/kurt/theories/`.

The banner's hash is the beginning of the SHA-256 of the exact `kurt.py` you're running. When
you compare unexpected behavior with someone else, it tells you whether you really run the same
code. To check it: `sha256sum kurt.py` (Linux), `shasum -a 256 kurt.py` (macOS),
`Get-FileHash kurt.py` (PowerShell) -- the first 12 characters are the banner's.

## License

[MIT](./LICENSE) © 2016-2026 Stefan Harmeling. When you use or cite Kurt, please link back to
this repository. A star on GitHub is also appreciated!
