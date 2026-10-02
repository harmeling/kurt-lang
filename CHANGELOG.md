# Changelog

## 0.7.0 (2026-10-02)

The first public release, after development since 2016. The language isn't frozen yet: a proof written for 0.7 may need small changes for 1.0.

### New

- **A kernel checks every step again.** Each step the search accepts comes with a certificate
  (which rule, which facts, which values), and a small checker verifies it without any search.
  This also covers closing blocks and `pick`. A step the kernel rejects is a `KernelError`,
  which no `expect` can catch. `cert N` shows the certificate of line `N`.
- **`.kurtc` files**: `kurt FILE.kurt` keeps the certificates of a completely checked file.
  The next run checks them with the kernel instead of searching. They are only hints: a
  changed file, or a certificate that doesn't check, just means searching again.
  `kurt --deps FILE.kurt` shows the tree of loaded files and whether their certificates are up
  to date, and `--no-kurtc` switches them off.
- **Each loaded file is checked on its own**, in a fresh context: only the core and what it
  loads itself. A library can't use its loader's facts, and the order of loads doesn't matter.
  Its exports must agree with the loader's symbols (the same declarations, the same `def`).
  Within a run, each library is checked once.
- `save "file.kurt"` writes the accepted lines of a file or a shell session, as Kurt source.
- Quantifiers and other binders with a condition, written in rules as `sub $x $v %C`, e.g.
  logic.kurt's "forall-cond-elim". There is a new theory, `analysis.kurt`: `abs`, finite sums,
  `max`/`min`, `sup`/`inf`, and limits by ε and δ, also with a condition.
- Tuples in set.kurt: `(a, b)`, "pair-eq", `fst`, `snd`, and `A × B`. The comma is
  right-associative, so `(a, b, c)` is `(a, (b, c))`. `f(a, b)` means `f a b`.
- `group.kurt`, with operator variables (`var ∘`, `infix ∘`) and operators as arguments:
  `group(R, (+), 0, (-))`.
- `calc`: theories bind their symbols to the built-in calculator (`calc + add, ...`), and
  numbers are exact (`0.1 + 0.2 = 0.3`, `1 / 3` stays a fraction). The calculator also works
  while a step is matched against a rule.
- `python -m kurt`, and a cookbook of recipes (`doc/kurt-cookbook.md`). New tutorial lessons:
  46-cert, 47-tuples, 48-groups.

### Changed (may need changes in existing proofs)

- `^` is right-associative and binds more tightly than the prefix `-`: `- 2 ^ 2` is `-4`, and
  `2 ^ 3 ^ 2` is `512`.
- arith.kurt: "pow-add" and "pow-mul" need a positive base (`$a > 0`), and `calc` doesn't
  compute `0 ^ 0`.
- `def` must be conservative: its left-hand side is the new symbol applied to distinct
  variables, and its right-hand side has no other variables. `def`, `load` and `chain` are not
  allowed inside proof blocks.
- A library must load what it uses itself (see "each loaded file is checked on its own").
- One `pick` per line. `save` writes only `.kurt` files, and works neither with `--strict` nor
  in a loaded file.
- `1.0` is the number `1`. set.kurt no longer declares `brackets [ ]`, which no fact used.
- The symbols of a theory that comes with Kurt can't be declared anew (`bool Nat`,
  `infix Nat 50 50`).

### Fixed

A targeted soundness review (September 2026) fixed every bug it found, each with a regression
test in `proofs/soundness/` or `tests/`. Among them:

- `def` wasn't conservative;
- the variables of assumptions and `let` conditions counted as "for all";
- `pick` witnesses could escape their block;
- set.kurt's separation didn't bind its variable, and its function extensionality was false;
- forged `.kurtc` files were accepted;
- several steps were accepted by the search but not by the kernel;
- lines that crashed Kurt instead of giving an error.

See `doc/kurt-soundness.md` §8.17.
