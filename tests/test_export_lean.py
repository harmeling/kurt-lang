import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from tests.utils import PROJECT_ROOT

# `kurt --lean FILE` (`export_lean`, before 2026-10-13 scripts/kurt2lean.py) writes a checked Kurt
# proof as a Lean 4 file; where Lean is installed (`lean` on the PATH, or ~/.elan/bin/lean), Lean
# checks it again -- otherwise only the translation itself is tested. The translation is tested with
# the Lean of scripts/lean-toolchain (the CI job `lean` installs it); an older Lean is skipped, since
# it may not know an option or a tactic the translation uses. KURT_REQUIRE_LEAN=1 (in CI): no Lean,
# or an older one, is an error.
#
# A proof that loads set.kurt or a number theory (set.kurt's `lean Obj ZFSet`: the objects are
# Mathlib's ZF sets, number.kurt's `lean real ℝ` the reals embedded into them) is written for Lean with
# Mathlib (`import Mathlib`): these exports are checked where the lake project scripts/lean is set
# up (`lake exe cache get`, see doc/kurt-ref.md `--lean`), by scripts/lean_check.py -- skipped
# otherwise; KURT_REQUIRE_MATHLIB=1 (the CI job `lean-mathlib`) makes a missing project an error.

KURT = PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py'
LEAN = shutil.which('lean') or next((p for p in [os.path.expanduser('~/.elan/bin/lean')] if os.path.isfile(p)), None)
TOOLCHAIN = (PROJECT_ROOT / 'scripts' / 'lean-toolchain').read_text(encoding='utf-8').strip()
_toolchain_version = re.search(r'v(\d+)\.(\d+)', TOOLCHAIN)
assert _toolchain_version is not None
TESTED = tuple(int(n) for n in _toolchain_version.groups())


def lean_version(lean_path):
    # (major, minor) of the Lean at `lean_path`, or None
    try:
        out = subprocess.run([lean_path, '--version'], capture_output=True, text=True, timeout=60).stdout
    except OSError:
        return None
    found = re.search(r'version (\d+)\.(\d+)', out)
    return tuple(int(n) for n in found.groups()) if found else None


sys.path.insert(0, str(PROJECT_ROOT / 'scripts'))
import lean_check                                   # (scripts/lean_check.py: Lean with Mathlib)
sys.path.pop(0)
MATHLIB = lean_check.mathlib_ready() and lean_check.elan_tool('lake') is not None
WHY_NOT_MATHLIB = f'the lake project with Mathlib is not set up ({lean_check.PROJECT}: lake exe cache get)'

VERSION = lean_version(LEAN) if LEAN else None
USABLE = VERSION is not None and VERSION >= TESTED
WHY_NOT = ('Lean is not installed' if not LEAN else
           f'Lean {VERSION} is older than {TOOLCHAIN} (scripts/lean-toolchain)')
# the proofs Lean checks completely (no `sorry`), each for what it needs of the translation
PROOFS = ['proofs/readme/contrapositive.kurt', 'proofs/natural-deduction/neg-forall.kurt',
          'proofs/natural-deduction/lemma.kurt',
          'proofs/natural-deduction/de-morgan.kurt',          # `case-elim`: the cases of a disjunction
          'proofs/natural-deduction/existsunique.kurt',       # `∃!` and a user's binder: higher-order constants
          'proofs/debug/def-in-a-block-logic.kurt']           # a `def` in a block (todo 77): an `obtain` in the proof
# the proofs with sets (set.kurt, so Lean with Mathlib: the sets of `ZFSet`) checked completely, with
# no `sorry` in the text either
SET_PROOFS = ['proofs/mafi1/07-groups.kurt',                      # `∃ $b ∈ G`, `pick` from it, a chain, `flat`
              'proofs/mafi1/15-inverse-matrix.kurt',              # `·` flat with three arguments: nested, with associativity
              'proofs/set-theory/function-space-membership.kurt', # `f a` and `f ∈ (A → B)`: `k_apply`; `let x ∈ ∅`
              'proofs/natural-numbers/peano.kurt',                # numerals without a theory of numbers: constants
              'proofs/mafi1/08-linear-span.kurt',                 # `def L($v1, $v2)`, a `def` over a pair: `L v1 v2`
              'proofs/mafi1/24-orthogonal-vectors.kurt',          # a conjunction after its lines `35a`, `35b`
              'proofs/mafi1/06-subspaces.kurt',                   # "vectorspace-intro", twelve premises: each on its own
              'proofs/mafi1/matrices.kurt',                       # `GL`, a token of Mathlib's: a name of its own
              'proofs/set-theory/power-set-membership.kurt',      # set.kurt's rules as theorems: `Pow`, `⊂`
              'proofs/set-theory/sets-by-their-elements.kurt',    # `{a, b, c}` Lean's own, the enumeration rules proved
              'proofs/logic-encodings/second-order-leibniz.kurt'] # a symbol `Obj` (the export's own name): renamed

# the proofs about numbers that Lean with Mathlib checks completely (no `sorry`, not even one of a
# calculation the tactics don't close), each for what it needs
MATHLIB_PROOFS = ['proofs/arithmetic/algebraic-identities.kurt',     # numerals, `+ - * /` of ℝ, `flat`/`sym` `+` as theorems
                  'proofs/arithmetic/chains.kurt',                   # `calc` by `norm_num`, a link of a chain `5 = 2 + 3 ≤ 7`
                  'proofs/arithmetic/factorial-with-calc.kurt',      # a fact that computes to the goal (`calc-fact`)
                  'proofs/arithmetic/exponent-laws.kurt',            # `^` as `Real.rpow`
                  'proofs/arithmetic/binomial-formulas.kurt',        # theorems of number.kurt (axioms here), "pow-two" by `Real.rpow_two`
                  'proofs/natural-numbers/gauss.kurt',               # natural.kurt: `Nat ⊂ ℝ`, induction a theorem
                  'proofs/natural-numbers/progressions.kurt',        # `6 ∈ Nat` by the calculator, `{a, b, ...}` a set of embedded numbers
                  'proofs/natural-numbers/sets-of-numbers-are-equal.kurt',  # "ext-real", `Nat ⊂ Real`, a chain of `⇔` (by `grind`)
                  'proofs/complex/complex-numbers.kurt',             # complex.kurt: `ℂ`, `+` of ℝ or of ℂ by the least sort, a real cast
                  'proofs/complex/powers-and-modulus.kurt',          # `k_cpow`, a complex rule for a real (`norm_cast`/`push_cast`), Gaussian `calc`
                  'proofs/debug/def-in-a-block.kurt',                # a `def` in a block (todo 77): numbers, a local function, a `let`/`pick`
                  'proofs/debug/pick-several-witnesses.kurt',        # `pick x, y, z with F`: nested blocks (todo 85)
                  'proofs/natural-numbers/intervals.kurt',           # interval.kurt: `Icc`, `Ioo`, ... by `k_numset`
                  ] + SET_PROOFS

# the theories of numbers (each loads number.kurt, `lean Obj ℝ`): their rules are theorems of
# Mathlib, each with its `lean "label" TACTIC` -- except these, which stay axioms in the export
LOGIC_THEORIES = ['propositional', 'logic', 'equality']    # their rules: theorems of Lean's logic, no Mathlib

# Kurt's theorems about `even`, `odd`, `∣`, `coprime`, `⊂`, each cited by a step (and the `def`s of
# these symbols: Lean `def`s -- `coprime($a, $b)` one over a pair)
DIVISIBILITY = '''load natural, divisibility
default real
const a, b, c, m, n, p, q, S
use n ∈ Nat "n"
use a ∈ Nat "a"
use m ∈ Nat "m"
use odd m "m-odd"
use even (p * p) "pp-even"
use p ∈ Nat "p"
use b ∣ c "bc"
use a ∣ b "ab"
use coprime(a, b) "a-b-coprime"
use even a "a-even"
use S ⊂ Nat "S-sub"
use c ∈ S "c-in-S"
use q ∈ Rat "q"
use q > 0 "q-pos"
even n ∨ odd n
¬(even m ∧ odd m)
odd (m * m)
even p
a ∣ a
1 ∣ a
a ∣ c
2 ∣ a
¬(even a ∧ even b)
∃ $x ($x ∈ S)
∃ $k ($k ∈ S ∧ ∀ $y ∈ S ($k <= $y))
∃ $i ∃ $j ($i ∈ Nat ∧ $j ∈ Nat ∧ $j ≠ 0 ∧ coprime($i, $j) ∧ q = $i / $j)
'''
DIVISIBILITY_THEOREMS = ['even-or-odd', 'not-even-and-odd', 'odd-square', 'even-square', 'divides-refl', 'one-divides',
                         'divides-trans', 'even-divides', 'coprime-not-both-even', 'well-ordering', 'lowest-terms']

NUMBER_THEORIES = ['number', 'natural', 'divisibility', 'interval', 'analysis', 'continuity', 'sequences', 'derivative', 'integral', 'set']
# the theories with a model in Lean (`lean Obj ...`): every rule proved there -- the numbers and sets in
# Mathlib's ZF sets, modal logic T in Kripke semantics (reflexive frames), the field axioms in the reals (the
# axiom audit, dev/todo.md 11)
THEORIES_WITH_A_MODEL = NUMBER_THEORIES + ['complex', 'modal', 'field']
STAY_AXIOMS = {
    # true (Riemann sums of a continuous function converge to its integral), but not in Mathlib
    'integral': {'integral-riemann'},
}

# what the translation writes for the constructs (checked on the text, without Lean)
EXPECTED_TEXT = {
    'proofs/mafi1/07-groups.kurt': ['(∃ (x', ' G) ∧ '],                                # `∃ $b ∈ G (...)` is `∃ b, b ∈ G ∧ ...`
    # `flat ·` in field.kurt's model (`lean · def ...`): its associativity a theorem, `U · A · B` nested
    'proofs/mafi1/15-inverse-matrix.kurt': ['theorem times_assoc', '(times_d2 x_U (times_d2 x_A x_B))'],
    'proofs/mafi1/06-subspaces.kurt': ['noncomputable def subspace (x', ' : Obj) : Prop := ', ' K_d0) → '],   # `def ... ⇔ ...` as a Lean `def`; `∀ $a ∈ K (...)`, `K` field.kurt's model
    'proofs/natural-deduction/existsunique.kurt': ['(∃ x_, ', '"existsunique-unique": proved in Lean'],   # `∃!` by its `lean` (logic.kurt)
    'proofs/mafi1/08-linear-span.kurt': ['noncomputable def L (x', ' : Obj) (x', '(L x_v1 x_v2)'],      # a `def` over a pair
    'proofs/natural-numbers/peano.kurt': ['axiom k_num_0 : Obj', 'axiom k_num_2 : Obj'],               # numerals, no number theory
    'proofs/natural-deduction/de-morgan.kurt': ['rcases d with h | h'],
    # a `def` in a block (todo 77): a local constant with its equation, a statement and a function too
    'proofs/debug/def-in-a-block-logic.kurt': ['obtain ⟨k, ', ' : ∃ (k : Prop), (k ↔ (P c)) :=', 'obtain ⟨m, ', 'obtain ⟨g_1, '],
    # a mapping applied: the `b` with `(a, b) ∈ f`, a definition; `A → B` the set of the mappings
    'proofs/set-theory/function-space-membership.kurt': ['noncomputable def k_apply (f a : Obj) : Obj', 'axiom f : Obj', '(ZFSet.funs A B)'],
    'proofs/mafi1/matrices.kurt': ['axiom k_GL : Obj'],
    # an object applied like a mapping: a term (`pairs(a) a`), a constant with a Lean meaning (`∅ a`), `k_apply`
    'proofs/debug/lean-object-applied.kurt': ['(k_apply (pairs a) a)', '(k_apply ((∅ : Obj)) a)'],
    'proofs/debug/lean-object-applied-mixed.kurt': ['(k_apply ((∅ : Obj)) a)'],
}

# sets and numbers in one proof: the numbers embedded into the sets (`k_emb`), a part of `Nat` by
# separation with the property read on the numbers (`k_lift`), `{1, ..., 5}` natural.kurt's set of
# embedded numbers, a pair of numbers -- and a rule of logic for numbers and sets alike (generic, `α`)
MIXED = '''load natural, interval
const A, B, c
use A = {1, 2} "A"
use B = { $n ∈ Nat | $n > 2 } "B"
use c ∈ Nat "c"
use c > 2 "c2"
1 ∈ {1, 2}
1 ∈ A
c ∈ Nat ∧ c > 2
c ∈ { $n ∈ Nat | $n > 2 }
c ∈ B
3 ∈ {1, ..., 5} ⇔ ∃ $k ∈ Nat (3 = 1 + $k ∧ 3 <= 5)
(1, c) ∈ Nat × Nat ⇔ 1 ∈ Nat ∧ c ∈ Nat
'''


def translate(proof: str, tmp: str) -> tuple[subprocess.CompletedProcess, str]:
    # `kurt --lean` on a copy of the proof in `tmp` (it writes the `.lean` next to the file) --
    # `cwd=tmp`: `load` looks in the working directory too (before the packaged theories), so
    # without it a file of the real cwd (wherever the suite happens to be invoked from) could be
    # found ahead of a sibling that isn't actually there, instead of this isolated `tmp`
    copy = os.path.join(tmp, 'proof.kurt')
    shutil.copy(PROJECT_ROOT / proof, copy)
    for sibling in (PROJECT_ROOT / proof).parent.glob('*.kurt'):     # what the proof may `load` (mafi1: `load matrices`)
        shutil.copy(sibling, tmp)
    result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', copy], capture_output=True, text=True, timeout=120, cwd=tmp)
    return result, os.path.join(tmp, 'proof.lean')


def export_text(source: str) -> str:
    # `kurt --lean` on a small proof: the text
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, 'proof.kurt')
        with open(path, 'w', encoding='utf-8') as fh:
            fh.write(source)
        result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', path], capture_output=True, text=True, timeout=120, cwd=tmp)
        assert result.returncode == 0, result.stderr
        return Path(tmp, 'proof.lean').read_text(encoding='utf-8')


def lean_mathlib(path: str) -> subprocess.CompletedProcess:
    command, cwd = lean_check.lean_command(Path(path))
    return subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=1200)


def lean(path: str) -> subprocess.CompletedProcess:
    assert LEAN is not None         # (the tests that call it are skipped without Lean)
    return subprocess.run([LEAN, os.path.basename(path)], cwd=os.path.dirname(path), capture_output=True, text=True, timeout=300)


# a conjunct of a long conjunction (todo 41): Kurt's flat `and` is in its own order (the assumption
# below is `A ∧ B ∧ C ∧ D ∧ E` for Kurt), Lean's `∧` right-nested -- the conjunct by its position
CONJUNCTS = '''load propositional
prop A, B, C, D, E
show A ∧ B ∧ C ∧ D ∧ E ⇒ D ∧ B "t"
proof
    assume E ∧ D ∧ C ∧ B ∧ A
        D
        B
        E
        D ∧ B
qed
'''


def only_projections(text: str) -> str:
    # the Lean text with the fallbacks after a projection (`| exact (f92).2.2.2.1`) removed: Lean
    # checks the projections themselves
    lines, out, skip = text.split('\n'), [], None
    for line in lines:
        if skip is not None and line.startswith(skip):
            continue
        skip = None
        out.append(line)
        if re.fullmatch(r'\s*\| exact \(\w+\)(\.[12])+', line):
            skip = line[:len(line) - len(line.lstrip())] + '| '
    return '\n'.join(out)


class TestExportLean(unittest.TestCase):
    def test_lean_is_there_where_required(self):
        if os.environ.get('KURT_REQUIRE_LEAN'):
            self.assertTrue(USABLE, WHY_NOT)

    def test_translates_completely(self):
        for proof in PROOFS + SET_PROOFS:
            with self.subTest(proof=proof), tempfile.TemporaryDirectory() as tmp:
                result, out = translate(proof, tmp)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('wrote', result.stdout)
                self.assertIn(result.stdout.strip().splitlines()[-1], (f'lean {out}', f'lake env lean {out}   # in a lake project with Mathlib'))   # the command, last
                text = open(out, encoding='utf-8').read()
                self.assertIn('theorem ', text)
                self.assertNotIn('sorry', text)

    def test_translates_the_constructs(self):
        # conditioned binders, `def`, `flat`/`sym`, other binders, `case`, a symbol applied and an object
        for proof, expected in EXPECTED_TEXT.items():
            with self.subTest(proof=proof), tempfile.TemporaryDirectory() as tmp:
                result, out = translate(proof, tmp)
                self.assertEqual(result.returncode, 0, result.stderr)
                text = open(out, encoding='utf-8').read()
                for piece in expected:
                    self.assertIn(piece, text)

    def test_the_type_of_the_objects(self):
        # a number theory's `lean Obj`: Mathlib's type for Kurt's objects, numerals of it, the
        # mapped symbols by their templates -- the theory that loads another one decides
        for theory, carrier in (('number', 'ℝ'), ('natural', 'ℝ'), ('divisibility', 'ℝ'), ('analysis', 'ℝ')):
            with self.subTest(theory=theory):
                text = export_text(f'load {theory}\nconst a, b\nuse a = b "given"\na + 1 = b + 1\n')
                self.assertTrue(text.startswith('import Mathlib\n'))
                self.assertIn('abbrev Obj : Type 1 := ZFSet.{0}', text)       # the objects: the sets
                self.assertIn('noncomputable def k_emb', text)                # ... the numbers embedded
                self.assertIn(f'axiom a : {carrier}', text)
                self.assertIn(f'(1 : {carrier})', text)
                self.assertRegex(text, rf'\(\(1 : {carrier}\) \+ a\)|\(a \+ \(1 : {carrier}\)\)')
                self.assertNotIn('axiom k_u2b :', text)                       # `+` is Mathlib's
                self.assertIn('theorem k_u2b_comm', text)                     # ... and `sym +` a theorem
        # without a number theory: no Mathlib, an opaque `Obj`
        text = export_text('load propositional\nprop A\nuse A\nA\n')
        self.assertNotIn('import Mathlib', text)
        self.assertIn('axiom Obj : Type', text)

    def test_the_rules_of_numbers_are_theorems(self):
        # a step by a rule of a number theory: the rule is a `theorem` with its proof in Lean (its
        # `lean "label" ...`), never an `axiom`; `Nat` by its one axiom, what `x ∈ Nat` means, and
        # what the calculator knows of it a theorem; the rules of a `chain` of Mathlib's relations too
        text = export_text('load number\nconst a, b\nuse a = b "given"\na + 1 = b + 1\n')
        self.assertIn('-- number.kurt:', text)
        self.assertRegex(text, r'"add-eq": proved in Lean .*\ntheorem f\d+ : .* := by\n  intros; subst_vars; rfl')
        self.assertNotRegex(text, r'axiom f\d+ : .*"add-eq"')
        text = export_text('load natural\nconst n\nuse n ∈ Nat "given"\nn + 1 ∈ Nat\ncalc on\n6 ∈ Nat\n')
        self.assertIn('abbrev Obj : Type 1 := ZFSet.{0}', text)
        self.assertIn('noncomputable def Nat : Obj := k_numset (fun (x : ℝ) => x ∈ Set.range (fun n : ℕ => (n : ℝ)))', text)
        self.assertIn('theorem k_mem_Nat : ∀ (x : ℝ), ((k_emb x) ∈ Nat) ↔ (x ∈ Set.range (fun n : ℕ => (n : ℝ)))', text)
        self.assertNotIn('axiom k_mem_Nat', text)
        self.assertRegex(text, r'"nat-(succ|add)": proved in Lean')
        self.assertNotRegex(text, r'axiom f\d+ : .*"nat-(succ|add|one)"')
        self.assertIn('theorem k_calc_Nat', text)
        self.assertNotIn('axiom k_calc_Nat', text)
        text = export_text('load number\nconst a, b, c\nuse a < b "ab"\nuse b <= c "bc"\na < c\n')
        self.assertRegex(text, r'"chain-trans-\d-\d": proved in Lean\ntheorem')
        self.assertNotRegex(text, r'axiom f\d+ : .*"chain-trans')
        # a `def` of a loaded file, as one of the file's own: a Lean `def`
        text = export_text('load natural, divisibility\nconst m\nuse m = 2 * 3 "m"\nuse 3 ∈ Nat "three"\nm = 2 * 3 ∧ 3 ∈ Nat\n3 ∈ Nat ∧ m = 2 * 3\n∃ $k ($k ∈ Nat ∧ m = 2 * $k)\neven m\n')
        self.assertIn('noncomputable def even', text)
        self.assertNotRegex(text, r'axiom f\d+ : .*"even-def"')

    def test_complex_numbers(self):
        # complex.kurt (todo 48): `lean complex ℂ`, a real where a complex number is required cast into
        # `ℂ`, an overloaded operator by the least sort of each occurrence -- `x ^ 2` of reals `Real.rpow`,
        # `z ^ 2` of a complex `z` `k_cpow` (`lean complex ^ ...`), `x + 1` in `ℝ`, `z + x` in `ℂ` --, a
        # complex number among the sets `k_embC` (a real embedded as itself); refused until 2026-10-23
        text = export_text('load complex\ncomplex z\nreal x\nuse z = x + 1 "zx"\nz + x = x + 1 + x\nx ^ 2 = x ^ 2\nz ^ 2 = z ^ 2\n')
        self.assertIn('noncomputable def k_embC (z : ℂ) : Obj', text)
        self.assertIn('noncomputable def k_cpow (z w : ℂ) : ℂ', text)
        self.assertIn('axiom z : ℂ', text)
        self.assertIn('axiom x : ℝ', text)
        self.assertRegex(text, r'\(\(\(x \+ \(1 : ℝ\)\) : ℝ\) : ℂ\)|\(\(\(\(1 : ℝ\) \+ x\) : ℝ\) : ℂ\)')   # `x + 1` of reals, then cast
        self.assertIn('(x ^ (2 : ℝ))', text)
        self.assertIn('(k_cpow z (2 : ℂ))', text)
        self.assertIn('theorem k_u2b_complex_comm : ∀ (a b : ℂ)', text)             # `sym +` in `ℂ` too
        self.assertNotIn('not translated', text)

    def test_sets_and_numbers_together(self):
        # the objects are Mathlib's ZF sets and the numbers the reals embedded into them (a
        # definition, injective: no axiom); a number where a set is required is `k_emb x`, the rules
        # of set.kurt are theorems about `ZFSet` -- none an axiom, none read over the reals any more
        text = export_text(MIXED)
        for piece in ('abbrev Obj : Type 1 := ZFSet.{0}', 'noncomputable def k_emb', 'theorem k_emb_injective',
                      '({(k_emb (1 : ℝ)), (k_emb (2 : ℝ))} : Obj)',                          # `{1, 2}`
                      'ZFSet.sep (fun (x', 'k_lift (fun (x',                                  # `{n ∈ Nat | n > 2}`
                      'k_numset (fun x_ => ∃ k_ : ℕ, x_ = (1 : ℝ) + k_ ∧ x_ ≤ (5 : ℝ))',     # `{1, ..., 5}`
                      '(ZFSet.pair (k_emb (1 : ℝ)) (k_emb c))', 'axiom c : ℝ', 'axiom A : Obj',
                      '∀ {α : Type u}, '):                                                 # "equal-elim" for numbers and sets
            self.assertIn(piece, text)
        for label in ('separation', 'element-1-of-2', 'product', 'range', 'equal-elim'):
            self.assertRegex(text, rf'"{label}": proved in Lean')
        self.assertNotRegex(text, r'^axiom f\d+ : .*-- axiom (set|natural|objects|logic|equality|propositional)\.kurt')
        self.assertNotIn('axiom k_in', text)
        self.assertNotIn('not translated', text)

    def test_every_rule_of_the_theories_of_numbers_is_proved(self):
        # each theory's own export (`kurt --lean number.kurt`): every `use` of the file a theorem with
        # its proof in Lean, but those of STAY_AXIOMS -- the text, without Lean
        theories = PROJECT_ROOT / 'src' / 'kurt' / 'theories'
        for theory in THEORIES_WITH_A_MODEL + ['finite']:     # (finite.kurt: its one rule, "nat-number")
            with self.subTest(theory=theory), tempfile.TemporaryDirectory() as tmp:
                source = (theories / f'{theory}.kurt').read_text(encoding='utf-8')
                rules = set(re.findall(r'^\s*use .*"([^"]+)"\s*(?:;.*)?$', source, re.MULTILINE))
                if theory == 'divisibility':
                    rules = set()       # (its theorems are proved by Kurt, no `use`: tested by DIVISIBILITY)
                else:
                    self.assertTrue(rules)
                out = os.path.join(tmp, f'{theory}.lean')
                result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', str(theories / f'{theory}.kurt'), '-o', out],
                                        capture_output=True, text=True, timeout=600)
                self.assertEqual(result.returncode, 0, result.stderr)
                text = Path(out).read_text(encoding='utf-8')
                proved = set(re.findall(rf'^-- {theory}\.kurt:\d+ "([^"]+)": proved in Lean', text, re.MULTILINE))
                left = set(re.findall(rf'^axiom f\d+ : .*-- axiom {theory}\.kurt:\d+ "([^"]+)"$', text, re.MULTILINE))
                self.assertEqual(rules - proved, STAY_AXIOMS.get(theory, set()))
                self.assertEqual(left & rules, STAY_AXIOMS.get(theory, set()))

    def test_every_rule_of_the_logical_theories_is_proved(self):
        # propositional.kurt, logic.kurt, equality.kurt exported on their own: every `use` a theorem of Lean's
        # logic (`lean "label" grind`), none an axiom -- and so is a step of a proof by one of them,
        # by a theorem of propositional.kurt ("excluded-middle"), by a `chain` of `=` (Lean's own); `∃!` and
        # `invimplies` by their `lean` (no Mathlib needed)
        theories = PROJECT_ROOT / 'src' / 'kurt' / 'theories'
        for theory in LOGIC_THEORIES:
            with self.subTest(theory=theory), tempfile.TemporaryDirectory() as tmp:
                source = (theories / f'{theory}.kurt').read_text(encoding='utf-8')
                rules = set(re.findall(r'^\s*use .*"([^"]+)"\s*(?:;.*)?$', source, re.MULTILINE))
                self.assertTrue(rules)
                out = os.path.join(tmp, f'{theory}.lean')
                result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', str(theories / f'{theory}.kurt'), '-o', out],
                                        capture_output=True, text=True, timeout=600)
                self.assertEqual(result.returncode, 0, result.stderr)
                text = Path(out).read_text(encoding='utf-8')
                self.assertNotIn('import Mathlib', text)
                proved = set(re.findall(rf'^-- {theory}\.kurt:\d+ "([^"]+)": proved in Lean', text, re.MULTILINE))
                self.assertEqual(rules - proved, set())
                self.assertNotRegex(text, r'^axiom f\d+ ')
        text = export_text('load logic\nconst a, b, c\nprop P\nuse a = b "ab"\nuse b = c "bc"\nuse P "p"\n'
                           'a = c\nP ∨ ¬P\n¬¬P\n∃ $x ($x = a)\n')
        self.assertNotRegex(text, r'^axiom f\d+ : .*-- axiom (propositional|logic|equality)\.kurt', )
        self.assertRegex(text, r'"excluded-middle": proved in Lean')
        self.assertRegex(text, r'"chain-trans-0-0": proved in Lean \(`lean|"chain-trans-0-0": proved in Lean\n')
        self.assertNotRegex(text, r'axiom f\d+ : .*"chain-trans')
        self.assertIn('axiom Obj : Type', text)

    def test_a_rule_proved_in_lean_has_the_definitions_it_unfolds(self):
        # number.kurt's "int-sub-real", `Int ⊂ Real`, is proved by unfolding set.kurt's `⊂`: its
        # export has the definition of `⊂`, not an axiom `subset` (that `simp only [subset]` can't open)
        theories = PROJECT_ROOT / 'src' / 'kurt' / 'theories'
        with tempfile.TemporaryDirectory() as tmp:
            out = os.path.join(tmp, 'number.lean')
            result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', str(theories / 'number.kurt'), '-o', out],
                                    capture_output=True, text=True, timeout=600)
            self.assertEqual(result.returncode, 0, result.stderr)
            text = Path(out).read_text(encoding='utf-8')
            self.assertIn('noncomputable def subset ', text)
            self.assertNotIn('axiom subset ', text)

    def test_theorems_about_divisibility(self):
        # a `def` over a pair, `def coprime($a, $b)`: a Lean function of two arguments; the `def`s of
        # the symbols in what a step cites (`even`, `∣`, `coprime`, `⊂`) are Lean `def`s, so Kurt's
        # theorems about them (natural.kurt, divisibility.kurt) are theorems with their `lean` proofs
        text = export_text(DIVISIBILITY)
        self.assertRegex(text, r'noncomputable def coprime \(x\d+ : ℝ\) \(x\d+ : ℝ\) : Prop')
        self.assertIn('(coprime a b)', text)
        for label in DIVISIBILITY_THEOREMS:
            self.assertRegex(text, rf'"{label}": proved in Lean', label)
        self.assertNotRegex(text, r'^axiom f\d+ : .*-- axiom (natural|divisibility)\.kurt')

    def test_numerals_without_a_theory_of_numbers(self):
        # a numeral where no theory gives `lean Obj` (field.kurt, peano's own `Nat`): a constant of its
        # own, one per number (Kurt reads `1.0` as `1`, `1.50` as `3/2`) -- no Mathlib
        text = export_text('load equality\nconst x, y\nuse x = 17 "x"\nuse y = 1.50 "y"\nuse x = 1.0 "one"\nuse 1 = 1.0 "same"\n17 = x\n')
        self.assertNotIn('import Mathlib', text)
        for piece in ('axiom k_num_17 : Obj', 'axiom k_num_3_div_2 : Obj', 'axiom k_num_1 : Obj', '(k_num_1 = k_num_1)'):
            self.assertIn(piece, text)
        self.assertNotIn('not translated', text)

    def test_a_conjunct_by_its_position(self):
        # "and-elim" from a flat conjunction: the conjunct picked by its position in Lean's
        # right-nested `∧`, before any search (todo 41: `simp` with `and_comm`, ... ran out of
        # heartbeats on vectorspace.kurt's twelve conjuncts)
        text = export_text(CONJUNCTS)
        self.assertIn('| exact (f', text)
        projections = re.findall(r'\| exact \(\w+\)((?:\.[12])+)\n', text)
        # (the assumption's parts, `5a`-`5e`: each conjunct of A ∧ B ∧ C ∧ D ∧ E)
        self.assertEqual(sorted(projections), ['.1', '.2.1', '.2.2.1', '.2.2.2.1', '.2.2.2.2'])

    def test_lean_declarations_of_the_file(self):
        # the file's own `lean` replaces the theory's: another type of the numbers, `- a` opaque (an
        # axiom of its own)
        text = export_text('load number\nlean real ℚ\nlean - opaque $1\nconst a\nuse a = 1 "given"\n-a = -1\n')
        self.assertIn('(1 : ℚ)', text)
        self.assertIn('axiom k_u2d_1 : ℚ → ℚ', text)
        self.assertIn('(k_u2d_1 a)', text)
        self.assertIn('(a - (1 : ℝ))', export_text('load number\nconst a\nuse a - 1 = 0\n'))   # `a - b` still Mathlib's

    def test_calculations_by_norm_num(self):
        # a `calc` step: the tactics in turn, a `sorry` last (Lean says so, it isn't hidden)
        text = export_text('load number\ncalc on\n2 + 3 = 5\n')
        self.assertIn('first | (norm_num; done)', text)
        self.assertIn('| sorry   -- a calculation', text)
        # without a number theory, a number is not translated
        self.assertNotIn('import Mathlib', export_text('load equality\nconst x\nuse x = 17\n'))

    @unittest.skipUnless(USABLE, WHY_NOT)
    def test_lean_checks_the_translation(self):
        for proof in PROOFS:
            with self.subTest(proof=proof), tempfile.TemporaryDirectory() as tmp:
                _, out = translate(proof, tmp)
                result = lean(out)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn('error', result.stdout)

    @unittest.skipUnless(USABLE, WHY_NOT)
    def test_lean_proves_the_logical_theories(self):
        # propositional.kurt, logic.kurt, equality.kurt on their own: Lean (no Mathlib) proves every rule
        theories = PROJECT_ROOT / 'src' / 'kurt' / 'theories'
        for theory in LOGIC_THEORIES:
            with self.subTest(theory=theory), tempfile.TemporaryDirectory() as tmp:
                out = os.path.join(tmp, f'{theory}.lean')
                result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', str(theories / f'{theory}.kurt'), '-o', out],
                                        capture_output=True, text=True, timeout=600)
                self.assertEqual(result.returncode, 0, result.stderr)
                checked = lean(out)
                self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
                self.assertNotIn('error', checked.stdout)
                self.assertNotIn('sorry', checked.stdout)

    @unittest.skipUnless(USABLE, WHY_NOT)
    def test_lean_checks_the_projections(self):
        # the projections of CONJUNCTS alone, without the fallbacks after them: Lean checks them
        with tempfile.TemporaryDirectory() as tmp:
            out = os.path.join(tmp, 'proof.lean')
            text = export_text(CONJUNCTS)
            projections = only_projections(text)
            self.assertEqual(text.count('\n') - projections.count('\n'), 5 * 4)   # five steps, four fallbacks each
            Path(out).write_text(projections, encoding='utf-8')
            result = lean(out)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('error', result.stdout)

    @unittest.skipUnless(USABLE, WHY_NOT)
    def test_lean_rejects_a_false_theorem(self):
        # the translation checks something: with the theorem changed into a false one (the
        # converse of the contrapositive), Lean fails -- at the theorem, for its type, while the
        # same file with the true theorem passes (so the failure isn't an option Lean doesn't know)
        with tempfile.TemporaryDirectory() as tmp:
            _, out = translate('proofs/readme/contrapositive.kurt', tmp)
            text = open(out, encoding='utf-8').read()
            true, false = '((A → B) → ((¬ B) → (¬ A)))', '((A → B) → ((¬ A) → (¬ B)))'
            self.assertIn('theorem f', text)
            self.assertIn(true, text)
            control = lean(out)
            self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
            with open(out, 'w', encoding='utf-8') as fh:
                fh.write(text.replace(true, false, 1))
            result = lean(out)
            self.assertNotEqual(result.returncode, 0)
            # (the closing `exact` has fallbacks for Kurt's normal forms, so the error Lean reports
            # is that of the last one, `grind failed`, at the false statement)
            self.assertIn('error', result.stdout + result.stderr)
            self.assertIn('¬A → ¬B', result.stdout + result.stderr)


class TestExportLeanMathlib(unittest.TestCase):
    def test_mathlib_is_there_where_required(self):
        if os.environ.get('KURT_REQUIRE_MATHLIB'):
            self.assertTrue(MATHLIB, WHY_NOT_MATHLIB)

    def test_the_toolchains_agree(self):
        # the lake project's Lean is the one of the plain tests, and Mathlib's tag is that version
        project = lean_check.PROJECT
        self.assertEqual((project / 'lean-toolchain').read_text(encoding='utf-8').strip(), TOOLCHAIN)
        self.assertIn(f'rev = "{TOOLCHAIN.split(":")[1]}"', (project / 'lakefile.toml').read_text(encoding='utf-8'))

    @unittest.skipUnless(MATHLIB, WHY_NOT_MATHLIB)
    def test_lean_with_mathlib_checks_the_translation(self):
        for proof in MATHLIB_PROOFS:
            with self.subTest(proof=proof), tempfile.TemporaryDirectory() as tmp:
                result, out = translate(proof, tmp)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn('lake env lean', result.stdout.strip().splitlines()[-1])
                self.assertTrue(Path(out).read_text(encoding='utf-8').startswith('import Mathlib'))
                checked = lean_mathlib(out)
                output = checked.stdout + checked.stderr
                self.assertEqual(checked.returncode, 0, output)
                self.assertNotIn('error', output)
                self.assertNotIn('declaration uses', output)          # no `sorry`, not even a calculation's

    @unittest.skipUnless(MATHLIB, WHY_NOT_MATHLIB)
    def test_lean_with_mathlib_checks_sets_and_numbers_together(self):
        # the proof of MIXED (sets and numbers): Lean checks it completely, every rule proved
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'proof.kurt')
            Path(path).write_text(MIXED, encoding='utf-8')
            result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', path], capture_output=True, text=True, timeout=600)
            self.assertEqual(result.returncode, 0, result.stderr)
            checked = lean_mathlib(os.path.join(tmp, 'proof.lean'))
            output = checked.stdout + checked.stderr
            self.assertEqual(checked.returncode, 0, output)
            self.assertNotIn('error', output)
            self.assertNotIn('declaration uses', output)

    @unittest.skipUnless(MATHLIB, WHY_NOT_MATHLIB)
    def test_lean_with_mathlib_checks_the_theories(self):
        # each theory of numbers, exported on its own: Lean proves its rules (`lean "label" ...`), and
        # checks the translation of its proofs -- no error (a `sorry` of a proof not translated is allowed)
        # (vectorspace.kurt: no rules of its own, but "vectorspace-intro"'s twelve conjuncts, todo 41)
        theories = PROJECT_ROOT / 'src' / 'kurt' / 'theories'
        for theory in THEORIES_WITH_A_MODEL + ['vectorspace']:
            with self.subTest(theory=theory), tempfile.TemporaryDirectory() as tmp:
                out = os.path.join(tmp, f'{theory}.lean')
                result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', str(theories / f'{theory}.kurt'), '-o', out],
                                        capture_output=True, text=True, timeout=600)
                self.assertEqual(result.returncode, 0, result.stderr)
                checked = lean_mathlib(out)
                output = checked.stdout + checked.stderr
                self.assertEqual(checked.returncode, 0, output)
                self.assertNotIn('error', output)

    @unittest.skipUnless(MATHLIB, WHY_NOT_MATHLIB)
    def test_lean_with_mathlib_proves_the_theorems_about_divisibility(self):
        # the proofs in Lean of divisibility.kurt's theorems about `even`, `odd`, `∣`,
        # `coprime`, `⊂` (`lean "even-square" ...`): Lean checks the export completely
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, 'proof.kurt')
            Path(path).write_text(DIVISIBILITY, encoding='utf-8')
            result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', path], capture_output=True, text=True, timeout=600)
            self.assertEqual(result.returncode, 0, result.stderr)
            checked = lean_mathlib(os.path.join(tmp, 'proof.lean'))
            output = checked.stdout + checked.stderr
            self.assertEqual(checked.returncode, 0, output)
            self.assertNotIn('error', output)
            self.assertNotIn('declaration uses', output)

    @unittest.skipUnless(MATHLIB, WHY_NOT_MATHLIB)
    def test_lean_with_mathlib_rejects_a_false_rule(self):
        # a theory's rule with a proof in Lean: Lean checks it -- a true one passes, a false one (with
        # the same tactic) is an error at its theorem, so `lean "label"` is checked, not trusted
        for rule, accepted in (('$a + 0 = $a', True), ('$a + 1 = $a', False)):
            with self.subTest(rule=rule), tempfile.TemporaryDirectory() as tmp:
                Path(tmp, 'mytheory.kurt').write_text(f'load number\nuse {rule} "my-rule"\nlean "my-rule" intros; ring\n', encoding='utf-8')
                Path(tmp, 'proof.kurt').write_text('load mytheory\nconst x\nx + 0 = x\n' if accepted else 'load mytheory\nconst x\nx + 1 = x\n', encoding='utf-8')
                result = subprocess.run([sys.executable, str(KURT), '--lean', '--no-kurtc', 'proof.kurt'], capture_output=True, text=True, timeout=120, cwd=tmp)
                self.assertEqual(result.returncode, 0, result.stderr)
                text = Path(tmp, 'proof.lean').read_text(encoding='utf-8')
                self.assertRegex(text, r'"my-rule": proved in Lean .*\ntheorem f\d+ : .*\n  intros; ring')
                checked = lean_mathlib(os.path.join(tmp, 'proof.lean'))
                output = checked.stdout + checked.stderr
                if accepted:
                    self.assertEqual(checked.returncode, 0, output)
                else:
                    self.assertNotEqual(checked.returncode, 0)
                    self.assertIn('error', output)

    @unittest.skipUnless(MATHLIB, WHY_NOT_MATHLIB)
    def test_lean_with_mathlib_rejects_a_false_theorem(self):
        # a false statement about numbers: the step by a rule fails (an error), while the true file
        # passes; a false calculation is left to its `sorry`, which Lean reports
        with tempfile.TemporaryDirectory() as tmp:
            _, out = translate('proofs/arithmetic/algebraic-identities.kurt', tmp)
            text = Path(out).read_text(encoding='utf-8')
            true = re.search(r'theorem f\d+ : \(\(\(2 : ℝ\) \* \(a \+ b\)\) = \(\(\(2 : ℝ\) \* a\) \+ \(\(2 : ℝ\) \* b\)\)\)', text)
            assert true is not None, 'the theorem `(a + b) * 2 = a * 2 + b * 2`'
            control = lean_mathlib(out)
            self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
            with open(out, 'w', encoding='utf-8') as fh:
                fh.write(text.replace(true.group(0), true.group(0).replace('((2 : ℝ) * b)', '((3 : ℝ) * b)'), 1))
            result = lean_mathlib(out)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('error', result.stdout + result.stderr)
        with tempfile.TemporaryDirectory() as tmp:
            _, out = translate('proofs/arithmetic/chains.kurt', tmp)
            text = Path(out).read_text(encoding='utf-8')
            calculation = re.search(r'theorem f\d+ : \(\(\(1 : ℝ\) \+ \(2 : ℝ\)\) = \(3 : ℝ\)\)', text)
            assert calculation is not None, 'the calculation `2 + 1 = 3`'
            with open(out, 'w', encoding='utf-8') as fh:
                fh.write(text.replace(calculation.group(0), calculation.group(0).replace('(3 : ℝ)', '(4 : ℝ)'), 1))
            result = lean_mathlib(out)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn('declaration uses', result.stdout + result.stderr)    # a `sorry`, not a proof


if __name__ == '__main__':
    unittest.main()
