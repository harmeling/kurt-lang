import copy
import io
import contextlib
import unittest

import kurt.kurt as kurt

from tests.utils import PROJECT_ROOT


def run_with_certificates(text: str, name: str = 'kernel-test.kurt') -> list[kurt.Certificate]:
    # run `text` as a file with `kernel_check` on, and return the certificates of its steps
    path = PROJECT_ROOT / 'tests' / name
    path.write_text(text)
    old = kurt.kernel_check
    kurt.kernel_check = True
    kurt.certificates.clear()
    try:
        kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            kurt.load_file(str(path), kb)
        return list(kurt.certificates)
    finally:
        kurt.kernel_check = old
        kurt.certificates.clear()
        path.unlink()


class TestCertificates(unittest.TestCase):
    def test_each_step_has_a_certificate(self):
        certs = run_with_certificates('\n'.join([
            'bool A, B',
            'use A implies B',
            'use A',
            'B',                  # by the rule `A implies B`, with the fact `A`
            'A',                  # an instance of a fact
            'true',               # top-intro
        ]))
        self.assertEqual([(c.kind, c.form) for c in certs], [('rule', 'impl'), ('rule', 'fact'), ('top', '')])
        impl = certs[0]
        self.assertEqual([f.label for f in impl.facts], [''])
        self.assertEqual(kurt.expr_str(impl.facts[0].expr, kurt.initial_kb), 'A')

    def test_values_of_a_schema_rule(self):
        certs = run_with_certificates('\n'.join([
            'load logic',
            'bool P',
            'arity P 1',
            'const P, c',
            'use forall x P x',
            'P c',                # an instance of the stored fact `P $x`
        ]))
        cert = certs[-1]
        self.assertEqual(cert.form, 'fact')
        self.assertIn(['c'], [[kurt.expr_str(v, kurt.initial_kb)] for v in cert.values.values()])


if __name__ == '__main__':
    unittest.main()
