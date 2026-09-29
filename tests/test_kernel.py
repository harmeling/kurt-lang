import copy
import io
import contextlib
import dataclasses
import unittest

import kurt.kurt as kurt

from tests.utils import PROJECT_ROOT


def run_with_certificates(text: str, name: str = 'kernel-test.kurt') -> list[kurt.Certificate]:
    # run `text` as a file, and return the certificates of its steps, in the order of the lines
    path = PROJECT_ROOT / 'tests' / name
    path.write_text(text)
    try:
        kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            kurt.load_file(str(path), kb)
        mine = sorted((line, certs) for (f, line), certs in kurt.certificates_by_line.items() if f == str(path))
        return [cert for _, certs in mine for cert, _ in certs]
    finally:
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


def check_during_run(text: str, variants) -> list[tuple[kurt.Certificate, dict]]:
    # run `text`; for each certificate, `variants(cert, kb)` gives changed
    # certificates by name, which are checked right away (the knowledge base changes later on) --
    # returns each certificate with the kernel's verdict on it (`'as is'`) and on its variants
    seen = []
    verify = kurt.kernel_verify
    def recording(cert, kb):
        verdicts = {'as is': verify(cert, kb)}
        for name, changed in variants(cert, kb).items():
            verdicts[name] = verify(changed, kb)
        seen.append((cert, verdicts))
        return verdicts['as is']
    kurt.kernel_verify = recording
    try:
        run_with_certificates(text)
    finally:
        kurt.kernel_verify = verify
    return seen


def token(name: str) -> kurt.Token:
    return kurt.Token('SYMBOL', name)


def value_named(cert, kb, text):
    return next(v for v in cert.values if kurt.expr_str(cert.values[v], kb) == text)


def fact_named(kb, text):
    return next(f for f in kb.all_theory() if kurt.expr_str(f.expr, kb) == text)


class TestKernelRejects(unittest.TestCase):
    # the certificates of real steps are accepted, and changing them in a way that makes the step
    # wrong gets them rejected

    def verdicts(self, text, variants, which=lambda cert: cert.kind == 'rule'):
        found = [v for cert, v in check_during_run(text, variants) if which(cert)]
        self.assertTrue(found, 'no such step')
        verdicts = found[0]
        self.assertIsNone(verdicts.pop('as is'))
        return verdicts

    def assert_rejected(self, verdicts, fragments):
        for name, fragment in fragments.items():
            self.assertIsNotNone(verdicts[name], f'the kernel accepts the wrong step "{name}"')
            self.assertIn(fragment, verdicts[name], name)

    def test_modus_ponens(self):
        def variants(cert, kb):
            copy_of_rule = kurt.Formula(kb, cert.rule.expr, '', '', '', '', '', '')
            copy_of_rule.simplified_expr = cert.expr
            return {'no facts': dataclasses.replace(cert, facts=[]),
                    'other goal': dataclasses.replace(cert, goal=token('A')),
                    'unknown rule': dataclasses.replace(cert, rule=copy_of_rule)}
        v = self.verdicts('bool A, B\nuse A implies B\nuse A\nB', variants)
        self.assert_rejected(v, {'no facts': 'does not follow', 'other goal': 'is not the goal',
                                 'unknown rule': 'not in the theory'})

    def test_free_variable_of_the_goal_gets_no_value(self):
        def variants(cert, kb):
            return {'value': dataclasses.replace(cert, values={**cert.values, **{y: token('c') for y in cert.fixed}})}
        v = self.verdicts('bool P\narity P 1\nconst P, c\nuse P $x\nP $y', variants)
        self.assert_rejected(v, {'value': 'got a value'})

    def test_premise_variable_stays_generic(self):
        # from `R $a c` the premise `∀ $x (R $x $T)` holds with `$T = c`; with the fact `R $b $b`,
        # `$T` would have to be the fresh variable for `$x` itself
        def variants(cert, kb):
            (e,) = cert.premise_fresh
            other = fact_named(kb, 'R $b $b')
            b = next(t.value for t in kurt.get_token_set(other.simplified_expr) if str(t.value).startswith('$'))
            values = {**cert.values, value_named(cert, kb, 'c'): token(e), b: token(e)}
            return {'eigen': dataclasses.replace(cert, facts=[other], values=values)}
        text = '\n'.join(['bool R, Q', 'arity R 2', 'const R, Q, c',
                          'use (∀ $x (R $x $T)) implies Q', 'use R $a c', 'use R $b $b', 'Q'])
        self.assert_rejected(self.verdicts(text, variants), {'eigen': 'depends on the fresh variables'})

    def test_no_capture(self):
        # `$T` in `∃ $y (R $y $T)` is one fixed term: it can't be the bound `$y`
        def variants(cert, kb):
            y = cert.expr[1][1].value
            other = fact_named(kb, '∃ $z (R $z $z)')
            values = {**cert.values, value_named(cert, kb, 'c'): token(y)}
            return {'capture': dataclasses.replace(cert, facts=[other], values=values)}
        text = '\n'.join(['bool R, Q', 'arity R 2', 'const R, Q, c',
                          'use (∃ $y (R $y $T)) implies Q', 'use ∃ $z (R $z c)', 'use ∃ $z (R $z $z)', 'Q'])
        self.assert_rejected(self.verdicts(text, variants), {'capture': 'capture'})

    def test_rule_with_sub(self):
        # "equal-elim", with a hole in the value of `%A`: another value for `$b` is rejected
        def variants(cert, kb):
            return {'other value': dataclasses.replace(cert, values={**cert.values, value_named(cert, kb, 'b'): token('a')})}
        text = 'load equality\nconst a, b, f\narity f 1\nuse a = b\nuse f a = a\nf b = a'
        v = self.verdicts(text, variants, lambda cert: cert.rule is not None and cert.rule.label == 'equal-elim')
        self.assert_rejected(v, {'other value': ''})



class TestKernelRejectsBlocks(unittest.TestCase):
    # closing `assume`, `let`, `pick`: real certificates are accepted, changed ones rejected

    def verdicts(self, text, kind, variants):
        found = [v for cert, v in check_during_run(text, variants) if cert.kind == kind]
        self.assertTrue(found, f'no {kind} step')
        verdicts = found[0]
        self.assertIsNone(verdicts.pop('as is'))
        return verdicts

    def assert_rejected(self, verdicts, fragments):
        for name, fragment in fragments.items():
            self.assertIsNotNone(verdicts[name], f'the kernel accepts the wrong step "{name}"')
            self.assertIn(fragment, verdicts[name], name)

    def test_impl_intro_and_not_intro(self):
        def variants(cert, kb):
            if cert.kind != 'impl-intro':
                return {}
            return {'other goal': dataclasses.replace(cert, goal=token('B')),
                    'not-intro': dataclasses.replace(cert, kind='not-intro', goal=[token('not'), token('A')])}
        text = 'load prop\nbool A, B\nuse A implies B\nassume A\n    B\ntrue'
        v = self.verdicts(text, 'impl-intro', variants)
        self.assert_rejected(v, {'other goal': 'is not', 'not-intro': 'not `false`'})

    def test_forall_intro(self):
        def variants(cert, kb):
            if cert.kind != 'forall-intro':
                return {}
            return {'no forall': dataclasses.replace(cert, goal=cert.rule.expr)}
        text = 'bool P\narity P 1\nconst P\nuse P $y\nlet x\n    P x\ntrue'
        self.assert_rejected(self.verdicts(text, 'forall-intro', variants), {'no forall': 'is not'})

    def test_exists_elim(self):
        def variants(cert, kb):
            if cert.kind != 'exists-elim':
                return {}
            return {'other goal': dataclasses.replace(cert, goal=[token('P'), token('c')]),
                    'not the last line': dataclasses.replace(cert, rule=cert.block.pick_fact)}
        text = 'load logic\nbool P, Q\narity P 1\nconst P, Q\nuse ∃ $x P $x\nuse P $y implies Q\npick c with P c\n    Q\nQ'
        v = self.verdicts(text, 'exists-elim', variants)
        self.assert_rejected(v, {'other goal': 'last line', 'not the last line': 'not the last line'})

    def test_no_constant_of_the_block_escapes(self):
        # a `pick` block whose last line mentions the witness `c` would let `c` escape (the
        # search never gets that far, so a fake last line `P c` is put into the block)
        verdicts = []
        verify = kurt.kernel_verify
        def recording(cert, kb):
            if cert.kind == 'exists-elim' and not verdicts:
                block = cert.block
                fake = kurt.Formula(block, block.pick_fact.expr, '', '', '', '', '', '')
                block.theory.append(fake)
                try:
                    verdicts.append(verify(dataclasses.replace(cert, rule=fake, goal=fake.expr), kb))
                finally:
                    block.theory.pop()
            return verify(cert, kb)
        kurt.kernel_verify = recording
        try:
            run_with_certificates('load logic\nbool P, Q\narity P 1\nconst P, Q\nuse ∃ $x P $x\nuse P $y implies Q\npick c with P c\n    Q\ntrue')
        finally:
            kurt.kernel_verify = verify
        self.assertTrue(verdicts)
        self.assertIsNotNone(verdicts[0], 'the witness escapes the `pick` block')
        self.assertIn('occur in', verdicts[0])


class TestCertCommand(unittest.TestCase):
    def output(self, text):
        path = PROJECT_ROOT / 'tests' / 'cert-test.kurt'
        path.write_text(text)
        try:
            kb = copy.deepcopy(kurt.initial_kb)
            out = io.StringIO()
            with contextlib.redirect_stdout(out), contextlib.redirect_stderr(io.StringIO()):
                try:
                    kurt.load_file(str(path), kb, mainstream=True)
                except kurt.KurtException:
                    pass
            return out.getvalue()
        finally:
            path.unlink()

    def test_cert_shows_the_certificate(self):
        out = self.output('bool A, B\nuse A implies B\nuse A\nB\ncert 4\ncert')
        self.assertEqual(out.count('; goal:      `B`'), 2)        # `cert` alone: the last line with a step
        self.assertIn('; rule:      `A implies B` (line 2)', out)
        self.assertIn('; premise:   `A` (line 3)', out)
        self.assertIn('; kernel:    checked', out)

    def test_names_as_written(self):
        out = self.output('load equality\nconst a, b, f\narity f 1\nuse a = b\nuse f a = a\nf b = a\ncert 6')
        self.assertIn('; rule:      `(($a = $b) and (sub $x $a %A)) implies (sub $x $b %A)`', out)
        self.assertIn('; values:    $a := `a`', out)
        self.assertNotIn('$$', out.split('cert 6')[-1])     # no internal names

    def test_a_failed_line_has_no_certificate(self):
        out = self.output('load prop\nbool A, B\nuse A\nexpect "ProofError"\n    A ∧ B\ncert 5')
        self.assertIn('; line 5: no certificate', out)


class TestKernelErrorStops(unittest.TestCase):
    # a step the kernel rejects doesn't count, also inside `expect`
    def run_rejecting(self, text):
        verify = kurt.kernel_verify
        kurt.kernel_verify = lambda cert, kb: 'rejected for the test'
        try:
            run_with_certificates(text)
        finally:
            kurt.kernel_verify = verify

    def test_kernel_error_stops_the_file(self):
        with self.assertRaises(kurt.KernelError) as e:
            self.run_rejecting('bool A\nuse A\nA ∧ A')
        self.assertIn('rejected for the test', e.exception.msg)
        self.assertEqual(e.exception.kind, 'KernelError')

    def test_expect_does_not_catch_it(self):
        with self.assertRaises(kurt.KurtException) as e:
            self.run_rejecting('bool A\nuse A\nexpect "ProofError"\n    A ∧ A')
        self.assertIn('KernelError', e.exception.msg)


if __name__ == '__main__':
    unittest.main()
