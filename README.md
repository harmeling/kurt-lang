# Kurt

Kurt is a small language for writing mathematical proofs in a form close to how people write
them — one claim per line, blocks for assumptions and cases — and a checker that tells you
immediately, line by line, whether each step follows. It is meant for students learning to prove
things, much like running tests while learning to program. Kurt has been developed by Stefan
Harmeling (TU Dortmund University) since 2016.

**Status: 0.7, a public beta.** Kurt is used for teaching, but the language isn't frozen yet: a
proof written for 0.7 may need small changes for 1.0.

Website: [www.kurt-lang.org](https://www.kurt-lang.org) (it leads here).

**Try it in your browser**, without installing anything:
[harmeling.github.io/kurt-web](https://harmeling.github.io/kurt-web/). The playground runs the same
Kurt in the browser, with the tutorial lessons and examples.

## A first proof

A file `modus-ponens.kurt`:

    ; simple modus ponens proof
    bool A, B
    use A implies B
    use A
    B

Check it on the command line:

    $ kurt modus-ponens.kurt
    This is Kurt, v0.7.0 (made by Stefan Harmeling, 2016-2026), file 014d63c1e32a
    use A implies B                           ; 3 without proof
    use A                                     ; 4 without proof
    B                                         ; 5 by 3(4)
    Proof checked

Each line gets the reason it holds: `B` follows by the rule of line 3 from the fact of line 4.
A proof with blocks, from the theory `prop` that comes with Kurt:

    ; if A implies B, then not B implies not A
    load prop
    bool A, B

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
  arithmetic, natural numbers with induction, analysis (sums, limits), and groups; and, as an
  experimental example, a fragment of modal logic.
  Even the grammar is declared there (`infix`, `bindop`, `chain`), so students can read why a
  step goes through.
- **A kernel checks every step again**: the search hands each accepted step to a small checker
  as a certificate. `cert N` shows the certificate of line `N`. The certificates of a checked
  file are kept in a `.kurtc` file, and next time the kernel checks them again, without any
  search.
- **Exact arithmetic** with `calc on`: `0.1 + 0.2 = 0.3` holds, and `1 / 3` stays a fraction.
- **For grading**: `kurt --strict` rejects axioms (`use`), `todo` and new rules outside the
  theories that come with Kurt.
- **No dependencies**: one Python file. It's also available as a single self-contained script
  with all theories embedded, to hand out in a course.

## Installing

With Python 3.10 or newer:

    pip install git+https://github.com/harmeling/kurt-lang.git

or a specific version, e.g. `...kurt-lang.git@v0.7.0`, or from a local clone with `pip install .`.
Then run `kurt` or `python -m kurt`.

**Without installing**, for a course: download the single self-contained `kurt.py` of the
latest release,

    https://github.com/harmeling/kurt-lang/releases/latest/download/kurt.py

It has all the theories embedded (`load prop` and so on work right away) and needs nothing but
Python: `python3 kurt.py proof.kurt`. You can also build it from this repository yourself, with
`python3 scripts/build_standalone.py` (writes `dist/kurt.py`). To keep the theories as separate, editable files instead,
copy `src/kurt/kurt.py` together with the directory `src/kurt/theories/`.

## Documentation

- [`tutorial/`](tutorial/): 49 short lessons (00 to 48), one keyword or idea each. Each one is a Kurt file
  you can run and change ([plan](tutorial/plan.md)).
- [`doc/kurt-cookbook.md`](doc/kurt-cookbook.md): recipes for common tasks. Prove an
  implication, argue by contradiction, split into cases, rewrite with equality, use induction,
  diagnose "can not derive".
- [`doc/kurt-doc.md`](doc/kurt-doc.md): the language reference.
- [`doc/kurt-soundness.md`](doc/kurt-soundness.md): what the checker's correctness rests on,
  rule by rule, and the bugs found so far, each with its regression test.
- [`proofs/`](proofs/): many more example proofs. Each one is also a test.

## Why trust it?

A checker is only useful if what it accepts is correct. In Kurt, every step the search finds is
checked again by the kernel. Loaded theories are checked on their own, independent of what was
loaded before. A `def` must be conservative. Adversarial test files (`proofs/soundness/`) keep
every bug found so far from coming back. Kurt is not a small-kernel system like Metamath or HOL
Light yet: the kernel still shares the parser and the normal forms with the search.
`doc/kurt-soundness.md` says exactly what is trusted.

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

The [kurt-syntax](https://github.com/harmeling/kurt-syntax) repository has editor support for
`.kurt` files: highlighting, comments and indentation, and, in VS Code and Emacs, LaTeX-style
shortcuts such as `\forall` → `∀`.

- **VS Code**: an extension with snippets, built with `npm install` and `npm run package`, then
  installed with `code --install-extension kurt-syntax-<version>.vsix`.
- **Emacs**: put `kurt-mode.el` and `replacements.json` together in a directory on your load
  path, and add `(require 'kurt-mode)` to your configuration.
- **Vim and Neovim**: use the repository as a plugin, e.g. clone it into
  `~/.vim/pack/plugins/start/kurt-syntax`, or into Neovim's plugin directory.

## Developing Kurt

    python -m venv .venv
    source .venv/bin/activate
    pip install -e .[dev]
    python -m unittest              # the test suite, including every file in proofs/
    coverage run -m unittest && coverage report

The implementation is the single file `src/kurt/kurt.py`. The theories are in
`src/kurt/theories/`.

The banner's `file <hash>` is a fingerprint of the exact `kurt.py` you're running. When you
compare unexpected behavior with someone else, it tells you whether you really run the same
code.

## License

[MIT](./LICENSE) © 2016-2026 Stefan Harmeling. When you use or cite Kurt, please link back to
this repository. A star on GitHub is also appreciated!
