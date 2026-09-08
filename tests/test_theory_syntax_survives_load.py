import copy
import re
import unittest
import importlib.resources as res

import kurt

# Regression test for a real class of bug found auditing the `local`/selective-export
# feature (doc/kurt-soundness.md #7): a symbol can have full syntax declared (`infix`,
# `prefix`, `postfix`) in a shipped theory, but if no *exported* (labelled, non-`local`) fact
# in that same file ever mentions it, its syntax is silently dropped when the theory is
# `load`ed -- even though the file's own source clearly intends the symbol to be usable
# (declaring `infix ^ 75 75` is not an accident). Found two real casualties this way: `^` in
# arith.kurt and `invimplies` in prop.kurt, both fixed by adding a genuine axiom that
# mentions the symbol. This test declares every `infix`/`prefix`/`postfix` symbol found in
# each shipped theory's own source text and asserts each one survived that file's `load`, so
# a future edit can't reintroduce this silently.

THEORIES = ['prop', 'equality', 'logic', 'set', 'arith', 'natural', 'modal']

# genuinely, deliberately unaxiomatized syntax -- set.kurt's own comment says mapping
# axioms ("two mappings are equal if they give the same output for all inputs") were never
# actually written, so `:`/`→` correctly don't survive `load set` right now; this isn't the
# oversight `^`/`invimplies` were, so it's exempted here rather than "fixed" with an invented
# axiom. Remove this exemption once set.kurt actually defines mapping equality.
KNOWN_UNAXIOMATIZED = {'set': {':', '→'}}

def declared_operators(theory: str) -> set[str]:
    path = res.files('kurt.theories').joinpath(f'{theory}.kurt')
    text = path.read_text()
    declared = set()
    for line in text.splitlines():
        line = line.split(';', 1)[0].strip()   # drop comments
        for kw in ('infix', 'prefix', 'postfix'):
            if line.startswith(kw + ' '):
                rest = line[len(kw):]
                for tok in re.split(r'[,\s]+', rest.strip()):
                    if tok and not tok.lstrip('-').isdigit():
                        declared.add(tok.strip('"'))
    return declared

class TestTheorySyntaxSurvivesLoad(unittest.TestCase):
    def test_every_declared_operator_survives_its_own_load(self):
        for theory in THEORIES:
            with self.subTest(theory=theory):
                kb = copy.deepcopy(kurt.initial_kb)
                kb = kurt.load_file(f'{theory}.kurt', kb, mainstream=False)
                exempt = KNOWN_UNAXIOMATIZED.get(theory, set())
                for op in declared_operators(theory) - exempt:
                    self.assertTrue(
                        kb.is_infix(op) or kb.is_prefix(op) or kb.is_postfix(op),
                        f"`{op}` is declared as syntax in {theory}.kurt but doesn't survive "
                        f"`load {theory}` -- no exported fact in the file mentions it, so its "
                        f"syntax is silently dropped (see doc/kurt-soundness.md #7)."
                    )

if __name__ == '__main__':
    unittest.main()
