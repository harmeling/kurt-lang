import contextlib
import copy
import io
import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt


class TestNaryCase(unittest.TestCase):
    def run_source(self, source: str):
        # (in a directory of its own: a file in tests/ was shared by parallel runs; resolved, as
        # Kurt names the file -- macOS's temporary directory is a symlink)
        tmp = tempfile.TemporaryDirectory()
        path = Path(tmp.name).resolve() / 'nary_case.kurt'
        path.write_text(source)
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                kurt.load_file(str(path), copy.deepcopy(kurt.initial_kb), main=True)
            return [cert for (name, _), entries in kurt.run_state.certificates_by_line.items()
                    if name == str(path) for cert, _ in entries]
        finally:
            tmp.cleanup()

    def test_five_case_blocks_combine(self):
        alternatives = ['A', 'B', 'C', 'D', 'E']
        lines = ['load propositional', 'prop ' + ', '.join(alternatives + ['G']),
                 'use ' + ' or '.join(alternatives)]
        lines += [f'use {a} implies G' for a in alternatives]
        for a in alternatives:
            lines += [f'case {a}', '    G']
        lines += ['G']
        certs = self.run_source('\n'.join(lines))
        cert = next(c for c in certs if c.kind == 'case-elim')
        self.assertEqual(len(cert.facts), 6)  # the disjunction and five discharged cases

    def test_many_alternatives_use_one_bounded_certificate(self):
        # This size is deliberately above the old hand-written 3/4-branch rules. The result has
        # one certificate with a linear-size fact list; no n-premise schema search is generated.
        alternatives = [f'A{i}' for i in range(40)]
        lines = ['load propositional', 'prop ' + ', '.join(alternatives + ['G']),
                 'use ' + ' or '.join(alternatives)]
        lines += [f'use {a} implies G' for a in alternatives]
        lines += ['G']
        certs = self.run_source('\n'.join(lines))
        cert = next(c for c in certs if c.kind == 'case-elim')
        self.assertEqual(len(cert.facts), 41)

    def test_missing_alternative_is_rejected(self):
        with self.assertRaises(kurt.KurtException) as caught:
            self.run_source('\n'.join([
                'load propositional', 'prop A, B, C, G', 'use A or B or C',
                'use A implies G', 'use B implies G', 'G',
            ]))
        self.assertEqual(caught.exception.kind, 'ProofError')

    def test_operator_merely_named_or_gets_no_builtin_meaning(self):
        # `case-elim` is derived from a known general binary rule. Merely declaring an unrelated
        # Boolean operator named `or` must not silently give it logical disjunction semantics.
        with self.assertRaises(kurt.KurtException) as caught:
            self.run_source('\n'.join([
                'infix or 14 14', 'prop or 0 1 2', 'flat or', 'sym or',
                'prop A, B, G', 'use A or B', 'use A implies G', 'use B implies G', 'G',
            ]))
        self.assertEqual(caught.exception.kind, 'ProofError')

    def test_an_own_or_gets_no_shortcut(self):
        # The shortcut needs the disjunction of a trusted theory (propositional.kurt's `builtin or
        # disjunction`), and its general elimination rule: a file's own `or` with its own rule
        # uses that rule as any other, but not the n-ary shortcut (2026-10-09: engine roles)
        certs = self.run_source('\n'.join([
            'infix or 14 14', 'prop or 0 1 2', 'flat or', 'sym or',
            'prop A, B, C', 'var A, B, C',
            'use (A or B) and (A implies C) and (B implies C) implies C',
            'prop P, Q, G', 'use P or Q', 'use P implies G', 'use Q implies G', 'G',
        ]))
        self.assertTrue(certs)      # (the certificates of this file: else the line below checks nothing)
        self.assertFalse(any(cert.kind == 'case-elim' for cert in certs))


if __name__ == '__main__':
    unittest.main()
