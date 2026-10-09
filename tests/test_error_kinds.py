import unittest

import kurt.kurt as kurt

# the kind of an error says at which stage a line failed (decided 2026-10-09, doc/kurt-doc.md §9.6):
# ScanError (a symbol), ParseError (reading the line), EvalError (readable, but not allowed --
# also wrong arguments of a keyword), TypeError, ProofError

CASES = [
    ('ScanError', 'bool A\nA ⊕ A\n'),                         # a character that isn't a symbol
    ('ParseError', 'bool A\n(A\n'),                           # a bracket that isn't closed
    ('ParseError', 'bool A\nA)\n'),                           # a bracket that isn't opened
    ('ParseError', 'bool A\n    A\n'),                        # indented without a block
    ('EvalError', 'summary 1\n'),                             # wrong arguments of a keyword
    ('EvalError', 'calc maybe\n'),
    ('EvalError', 'cert x\n'),
    ('EvalError', 'show true, true\n'),
    ('TypeError', 'use $A implies $A\n'),                    # a term variable where a formula belongs
    ('ProofError', 'bool A\nA\n'),                            # can't be derived
]


class TestErrorKinds(unittest.TestCase):
    def test_each_stage_has_its_kind(self):
        for kind, text in CASES:
            with self.subTest(text=text):
                result = kurt.check_text(text)
                self.assertEqual(result.error_kind, kind, result.error)

    def test_the_kinds(self):
        self.assertEqual(set(kurt.KurtException.KNOWN_KINDS), {'ScanError', 'ParseError', 'EvalError', 'TypeError', 'ProofError'})

if __name__ == '__main__':
    unittest.main()
