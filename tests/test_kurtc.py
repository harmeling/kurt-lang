import copy
import dataclasses
import io
import json
import contextlib
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import kurt.kurt as kurt
from tests.utils import numbered, PROJECT_ROOT


class KurtcTestCase(unittest.TestCase):
    # runs files in a temporary directory, with `.kurtc` files on (as `kurt` on the command line)
    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        # resolved once: kurt resolves the path of the file it checks (`run_state.current_line`),
        # so an unresolved temp dir (macOS's /tmp is a symlink to /private/tmp) would make a
        # stored certificate's file field never match a formula's -- resolve_formula finds nothing
        self.dir_path = os.path.realpath(self.dir.name)
        self.old = kurt.run_state.kurtc_enabled
        kurt.run_state.kurtc_enabled = True

    def tearDown(self):
        kurt.run_state.kurtc_enabled = self.old
        kurt.run_state.replay_hints.clear()
        self.dir.cleanup()

    def write(self, name: str, text: str) -> Path:
        path = Path(self.dir_path) / name
        path.write_text(text)
        return path

    def run_file(self, path: Path) -> str:
        kb = copy.deepcopy(kurt.initial_kb)
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            kurt.load_file(str(path), kb, main=True)
        return out.getvalue()


class TestWriting(KurtcTestCase):
    def test_a_checked_file_gets_a_kurtc(self):
        path = self.write('mp.kurt', 'prop A, B\nuse A implies B\nuse A\nB\n')
        self.run_file(path)
        content = json.loads(Path(str(path) + 'c').read_text())
        self.assertEqual(content['kurtc'], kurt.KURTC_VERSION)
        self.assertEqual(content['sha256'], kurt.source_hash(str(path)))
        self.assertEqual(list(content['steps']), ['4'])
        step = content['steps']['4'][0]
        self.assertEqual(step['rule']['line'], '2')
        self.assertEqual([f['line'] for f in step['facts']], ['3'])

    def test_no_kurtc_with_a_todo(self):
        path = self.write('todo.kurt', 'prop A\ntodo\nA\n')
        self.run_file(path)
        self.assertFalse(Path(str(path) + 'c').exists())

    def test_dependencies_are_listed(self):
        self.write('lemma.kurt', 'prop A\nuse A "a"\n')
        path = self.write('main.kurt', 'load lemma\nA\n')
        self.run_file(path)
        content = json.loads(Path(str(path) + 'c').read_text())
        self.assertEqual([Path(d['file']).name for d in content['depends']], ['lemma.kurt'])


    def test_unchanged_certificates_are_not_written_again(self):
        # (every run wrote the `.kurtc` of each file again, 0.5 s for `load rational`)
        path = self.write('mp.kurt', 'prop A, B\nuse A implies B\nuse A\nB\n')
        self.run_file(path)
        kurtc = Path(str(path) + 'c')
        os.utime(kurtc, ns=(1_000_000_000, 1_000_000_000))
        self.run_file(path)
        self.assertEqual(kurtc.stat().st_mtime_ns, 1_000_000_000)
        path.write_text('prop A, B\nuse A implies B\nuse A\nB\nB\n')
        self.run_file(path)
        self.assertNotEqual(kurtc.stat().st_mtime_ns, 1_000_000_000)      # (changed: written)

    def test_a_theory_of_kurt_is_named_without_its_place(self):
        # so that the certificates of the theories fit wherever Kurt is (the package, the bundle)
        path = self.write('eq.kurt', 'load equality\nconst a, b, f\narity f 1\nuse a = b\nf a = f b\n')
        self.run_file(path)
        content = json.loads(Path(str(path) + 'c').read_text())
        self.assertEqual(content['steps']['5'][0]['rule']['file'], '<kurt>/equality.kurt')     # (equal-elim)
        self.assertEqual(content['depends'][0]['file'], '<kurt>/equality.kurt')


class TestReplay(KurtcTestCase):
    def count_searches(self, path: Path, function: str = 'impl_elim') -> tuple[str, int]:
        # the output, and how often the search (`impl_elim`, or another `function` of it) runs
        calls = [0]
        original = getattr(kurt, function)
        def counting(*args, **kwargs):
            calls[0] += 1
            return original(*args, **kwargs)
        setattr(kurt, function, counting)
        try:
            return self.run_file(path), calls[0]
        finally:
            setattr(kurt, function, original)

    def test_second_run_needs_no_search(self):
        path = self.write('eq.kurt', 'load equality\nconst a, b, f\narity f 1\nuse a = b\nuse f a = a\nf b = a\nb = a\n')
        out1, searches1 = self.count_searches(path)
        out2, searches2 = self.count_searches(path)
        self.assertEqual(out1, out2)
        self.assertGreater(searches1, 0)
        self.assertEqual(searches2, 0)

    def test_a_chain_step_replays_with_its_instance(self):
        # the certificate of a chain line cites the instance the search derived first (`8a`, see
        # `conditional_rewrite`), a step of the line itself: on the next run it is derived from its
        # own certificate before the line's (`replay_step`) -- no search at all, the same output
        # (until 2026-10-16 the line's certificate failed, since `8a` wasn't there, and field.kurt
        # took 4.9 s with its certificates)
        path = self.write('chain.kurt', 'load field\nconst x\nuse x ∈ K\n- 1 ∈ K\nx + 1 ∈ K\n'
                                        '(x + 1) · (- 1) ∈ K\n(x + 1) · x ∈ K\n'
                                        '(x + 1) · (x + (- 1)) = (x + 1) · x + (x + 1) · (- 1)\n'
                                        '                      = (x · x + 1 · x) + (x + 1) · (- 1)\n')
        self.run_file(self.write('warm.kurt', 'load field\n'))      # (field.kurt checked: only the lines below count)
        out1, searches1 = self.count_searches(path, 'match_all_theory')
        self.assertIn('9a by distributive-right', out1)
        out2, searches2 = self.count_searches(path, 'match_all_theory')
        self.assertEqual(out1, out2)
        self.assertGreater(searches1, 0)
        self.assertEqual(searches2, 0)
        kurtc = Path(str(path) + 'c')
        stored = json.loads(kurtc.read_text())
        self.assertEqual([h['rule']['label'] for h in stored['steps']['9']], ['distributive-right', 'equal-elim'])   # the step's, the line's
        stamp = kurtc.stat().st_mtime_ns
        self.run_file(path)
        self.assertEqual(kurtc.stat().st_mtime_ns, stamp)            # (the replay gives the same certificates: not written again)

    def test_a_line_rewriting_two_places_replays_with_its_step(self):
        # `multi_rewrite`: the line with one place rewritten is a step (`5a`), and the line's
        # certificate cites it
        path = self.write('two.kurt', 'load numbers\nconst x, y\nuse x = 0\nuse y = 0\nx + y = 0 + 0\n')
        self.run_file(self.write('warm.kurt', 'load numbers\n'))
        out1, searches1 = self.count_searches(path, 'match_all_theory')
        self.assertIn('5a by equal-elim', out1)
        out2, searches2 = self.count_searches(path, 'match_all_theory')
        self.assertEqual(out1, out2)
        self.assertGreater(searches1, 0)
        self.assertEqual(searches2, 0)

    def test_a_step_without_its_certificate_is_searched(self):
        # the step's certificate taken out of the `.kurtc`: the line's can't be rebuilt, the search
        # runs (and finds the same), nothing is accepted without the kernel
        path = self.write('two.kurt', 'load numbers\nconst x, y\nuse x = 0\nuse y = 0\nx + y = 0 + 0\n')
        out1 = self.run_file(path)
        kurtc = Path(str(path) + 'c')
        content = json.loads(kurtc.read_text())
        content['steps']['5'] = [h for h in content['steps']['5'] if h['rule']['label'] != 'equal-elim' or h['facts'][0]['line'] != '5a'][-1:]
        self.assertEqual(len(content['steps']['5']), 1)
        kurtc.write_text(json.dumps(content))
        out2, searches2 = self.count_searches(path, 'match_all_theory')
        self.assertEqual(out1, out2)
        self.assertGreater(searches2, 0)

    def test_conditional_rewriting_checks_again(self):
        # the certificate of a rewriting step with a derived instance (`7a`) refers to that step,
        # which doesn't exist yet on the next run -- then the search has to be the full one again
        # (it used to be the plain one, without the shortcuts, and failed)
        path = self.write('cr.kurt', 'load set\ninfix · 70 70\nconst K, a, b, c\nuse $a ∈ K  ⇒  $a · 1 = $a  "K7"\n'
                                     'use b ∈ K\nuse c · (b · 1) = a\nc · b = a\n')
        self.run_file(path)
        self.assertTrue(Path(str(path) + 'c').exists())
        self.assertIn('7a by K7', self.run_file(path))

    def test_changed_source_ignores_the_kurtc(self):
        path = self.write('mp.kurt', 'prop A, B\nuse A implies B\nuse A\nB\n')
        self.run_file(path)
        path.write_text('prop A, B\nuse A implies B\nuse A\nB\nB\n')
        _, searches = self.count_searches(path)
        self.assertGreater(searches, 0)

    def test_forged_kurtc_proves_nothing(self):
        # a `.kurtc` with the right hash, but a certificate for a false claim: `B` from `A`
        good = self.write('good.kurt', 'prop A, B\nuse A implies B\nuse A\nB\n')
        self.run_file(good)
        forged = json.loads(Path(str(good) + 'c').read_text())
        bad = self.write('bad.kurt', 'prop A, B\nuse B implies A\nuse A\nB\n')     # `B` doesn't follow
        forged['sha256'] = kurt.source_hash(str(bad))
        forged['steps']['4'][0]['rule']['file'] = str(bad)
        forged['steps']['4'][0]['facts'][0]['file'] = str(bad)
        # the stored rule is exactly line 2 of `bad.kurt`, so it is found -- only the kernel can object
        forged['steps']['4'][0]['rule']['expr'] = {'e': [['SYMBOL', 'implies'], ['SYMBOL', 'B'], ['SYMBOL', 'A']]}
        Path(str(bad) + 'c').write_text(json.dumps(forged))
        verdicts = []
        verify = kurt.kernel_verify
        def recording(cert, kb):
            verdicts.append(verify(cert, kb))
            return verdicts[-1]
        kurt.kernel_verify = recording
        try:
            with self.assertRaises(kurt.KurtException) as e:
                self.run_file(bad)
        finally:
            kurt.kernel_verify = verify
        self.assertIn('can not derive', e.exception.msg)
        self.assertTrue(any(v is not None and 'not the goal' in v for v in verdicts), verdicts)   # the kernel said no

    def test_damaged_kurtc_is_ignored(self):
        path = self.write('mp.kurt', 'prop A, B\nuse A implies B\nuse A\nB\n')
        self.run_file(path)
        content = json.loads(Path(str(path) + 'c').read_text())
        content['steps']['4'][0]['values'] = 'nonsense'
        Path(str(path) + 'c').write_text(json.dumps(content))
        self.assertTrue(numbered(self.run_file(path), 4, 'by 2(3)'))


class TestDependencies(KurtcTestCase):
    def test_tree_with_status(self):
        self.write('a.kurt', 'prop A\nuse A "a"\n')
        self.write('b.kurt', 'load a\nprop B\nuse A implies B "b"\n')
        main = self.write('main.kurt', 'load a, b\nB\n')
        self.assertIn('main.kurt  -- not certified', kurt.dependencies_str(str(main)))
        self.run_file(main)
        tree = kurt.dependencies_str(str(main)).splitlines()
        self.assertTrue(tree[0].startswith('main.kurt  -- certified'), tree)
        self.assertTrue(tree[1].startswith('├─ a.kurt  -- certified'), tree)
        self.assertTrue(tree[2].startswith('└─ b.kurt  -- certified'), tree)
        self.assertEqual(tree[3], '   └─ a.kurt  (see above)')
        (Path(self.dir_path) / 'a.kurt').write_text('prop A\nuse A "a"\n; changed\n')
        tree = kurt.dependencies_str(str(main)).splitlines()
        self.assertIn('certified, but a.kurt changed since', tree[0])
        self.assertIn('out of date: the file changed since', tree[1])


def theory_line(theory: str, label: str) -> tuple[str, str]:
    # the file (as Kurt names it) and the line of the formula with `label` in a packaged theory
    path = kurt.resolve_load(theory, __file__)
    assert path is not None, f'no theory {theory}'
    with open(path) as fh:
        for n, text in enumerate(fh, start=1):
            if f'"{label}"' in text:
                return path, str(n)
    raise AssertionError(f'no "{label}" in {theory}')


class TestForgedCertificates(KurtcTestCase):
    # the forgeries found in the soundness review of 2026-09-29: each one used to prove `0 = 1`
    # with the right hash -- now the line they are for is simply not derivable
    def forge(self, path: Path, line: str, step: dict) -> None:
        content = {'kurtc': kurt.KURTC_VERSION, 'kurt': 'forged', 'source': path.name,
                   'sha256': kurt.source_hash(str(path)), 'depends': [], 'steps': {line: [step]}}
        Path(str(path) + 'c').write_text(json.dumps(content))

    def test_no_value_for_a_constant(self):
        # "empty-set" `not ($x ∈ ∅)` with `∅ := Nat` would give `not (0 ∈ Nat)`
        path = self.write('b.kurt', 'load natural\nnot (0 ∈ Nat)\n')
        file, line = theory_line('set', 'empty-set')
        S = lambda v: ['SYMBOL', v]
        E = lambda *c: {'e': list(c)}
        self.forge(path, '2', {'goal': E(S('not'), E(S('in'), ['INT', 0], S('Nat'))),
                               'rule': {'file': file, 'line': line, 'label': 'empty-set', 'direction': None,
                                        'expr': E(S('not'), E(S('in'), S('$$c0'), S('$$c1')))},
                               'form': 'fact', 'facts': [], 'premise_fresh': [], 'conclusion_fresh': [], 'fact_fresh': [],
                               'values': [['$$c0', ['INT', 0]], ['$$c1', S('Nat')]]})
        with self.assertRaises(kurt.KurtException) as e:
            self.run_file(path)
        self.assertIn('can not derive', e.exception.msg)

    def test_direction_only_of_an_iff(self):
        # "bottom-elim" `false ⇒ %A` read backwards would give `false` from any fact
        path = self.write('h.kurt', 'load numbers\nfalse\n')
        file, line = theory_line('propositional', 'bottom-elim')
        fact_file, fact_line = theory_line('numbers', 'factorial-base')
        S = lambda v: ['SYMBOL', v]
        E = lambda *c: {'e': list(c)}
        fact = E(S('='), E(S('!'), ['INT', 0]), ['INT', 1])
        self.forge(path, '2', {'goal': S('false'),
                               'rule': {'file': file, 'line': line, 'label': 'bottom-elim', 'direction': 'rl',
                                        'expr': E(S('implies'), S('false'), S('%%c0'))},
                               'form': 'impl', 'facts': [{'file': fact_file, 'line': fact_line, 'label': 'factorial-base',
                                                          'direction': None, 'expr': fact}],
                               'premise_fresh': [], 'conclusion_fresh': [], 'fact_fresh': [],
                               'values': [['%%c0', fact]]})
        with self.assertRaises(kurt.KurtException) as e:
            self.run_file(path)
        self.assertIn('can not derive', e.exception.msg)

    def test_kernel_rejects_them_directly(self):
        # also without the checks of the replay: the kernel itself
        verdicts = {}
        verify = kurt.kernel_verify
        def recording(cert, kb):
            if cert.kind == 'rule' and cert.form == 'fact' and not verdicts:
                values = {**cert.values, 'Nat': kurt.Token('SYMBOL', 'c')}
                verdicts['constant'] = verify(dataclasses.replace(cert, values=values), kb)
                clone = cert.rule.clone(['implies', cert.expr, cert.expr], kb)
                clone.direction_of = cert.rule.simplified_expr         # not an `iff`
                clone.simplified_expr = [kurt.Token('SYMBOL', 'implies'), cert.expr, cert.expr]
                verdicts['direction'] = verify(dataclasses.replace(cert, rule=clone, expr=clone.simplified_expr), kb)
            return verify(cert, kb)
        kurt.kernel_verify = recording
        try:
            self.run_file(self.write('k.kurt', 'load natural\n0 ∈ Nat\n'))
        finally:
            kurt.kernel_verify = verify
        self.assertIn('only variables get values', verdicts['constant'])
        self.assertIn('not in the theory', verdicts['direction'])


class TestCache(unittest.TestCase):
    # the theories in a directory without write access (an installed Kurt): their certificates
    # go to the cache directory, and are used from there
    def test_certificates_of_a_read_only_theory_go_to_the_cache(self):
        if hasattr(os, 'geteuid') and os.geteuid() == 0:
            self.skipTest('root may write anywhere')
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            shutil.copy(PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py', root / 'kurt.py')
            theories = root / 'theories'
            shutil.copytree(PROJECT_ROOT / 'src' / 'kurt' / 'theories', theories, ignore=shutil.ignore_patterns('*.kurtc'))
            (root / 'work').mkdir()
            (root / 'work' / 'p.kurt').write_text('load set\nconst A\nA = A\n')
            theories.chmod(0o555)
            try:
                env = dict(os.environ, XDG_CACHE_HOME=str(root / 'cache'))
                env.pop('PYTHONPATH', None)
                def run():
                    result = subprocess.run([sys.executable, str(root / 'kurt.py'), 'p.kurt'], cwd=root / 'work',
                                            env=env, capture_output=True, text=True, timeout=120)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                run()
                cached = sorted(p.name.split('-', 1)[1] for p in (root / 'cache' / 'kurt').iterdir())
                self.assertIn('set.kurtc', cached)
                self.assertEqual(list(theories.glob('*.kurtc')), [])
                stamps = {p: p.stat().st_mtime_ns for p in (root / 'cache' / 'kurt').iterdir()}
                run()
                self.assertEqual(stamps, {p: p.stat().st_mtime_ns for p in (root / 'cache' / 'kurt').iterdir()})
            finally:
                theories.chmod(0o755)


if __name__ == '__main__':
    unittest.main()
