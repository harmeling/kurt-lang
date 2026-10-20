import os
import tempfile
import unittest

import kurt
import kurt.kurt as internals

# the time of `load` with the theories checked already (todo 26, 2026-10-16): the theories that
# come with Kurt are looked up once, and a bundle taken from the cache shares its formulas


class TestPackagedTheoryLookup(unittest.TestCase):
    def test_a_packaged_theory_is_looked_up_once(self):
        # `is_file` of a packaged path lists the directory each time (3 ms; 280 times for `load rational`)
        first = internals.packaged_theory_file('propositional.kurt')
        self.assertIsNotNone(first)
        self.assertIs(internals.packaged_theory_file('propositional.kurt'), first)
        self.assertIsNone(internals.packaged_theory_file('no-such-theory.kurt'))
        self.assertIsNone(internals.packaged_theory_file('sub/propositional.kurt'))     # (a name with a directory is never packaged)

    def test_the_answer_depends_on_the_paths(self):
        # the standalone bundle appends its embedded theories to `packaged_theory_paths`
        before = list(internals.packaged_theory_paths)
        try:
            internals.packaged_theory_paths.append(internals.EmbeddedTheories({'extra.kurt': 'prop A\n'}))
            self.assertIsNotNone(internals.packaged_theory_file('extra.kurt'))
        finally:
            internals.packaged_theory_paths[:] = before
        self.assertIsNone(internals.packaged_theory_file('extra.kurt'))


class TestSharedFormulas(unittest.TestCase):
    def test_a_cached_bundle_shares_its_formulas(self):
        # the second file of a session that loads the same theory gets the cached bundle: its tables
        # are copies (the loader adds to them), its formulas the very objects of the cache -- a
        # `Formula` is never changed once it is in a theory, and copying 200 of them was most of
        # the time of a `load` from the cache
        with tempfile.TemporaryDirectory() as tmp:
            for name in ('one', 'two'):
                with open(os.path.join(tmp, f'{name}.kurt'), 'w', encoding='utf-8') as f:
                    f.write('load propositional\nprop A\nuse A\nA or A\n')
            session = kurt.new_session(kurt.RunConfig())
            self.assertTrue(session.check_file(os.path.join(tmp, 'one.kurt')).ok)
            (cached_bundle, _, _), = [v for k, v in session._state._checked_exports.items() if k[0].endswith('propositional.kurt')]
            self.assertTrue(session.check_file(os.path.join(tmp, 'two.kurt')).ok)
            kb = session.last_kb
            cached = {id(f) for f in cached_bundle.theory}
            shared = [f for f in kb.all_theory() if id(f) in cached]
            self.assertEqual(len(shared), len(cached_bundle.theory))      # (every exported fact of propositional.kurt, also the generated chain rules)
            self.assertIsNot(kb.theory, cached_bundle.theory)
            self.assertIsNot(kb.prop, cached_bundle.prop)

    def test_the_bundle_in_the_cache_is_not_the_files(self):
        # (the file's level is discarded; the cache keeps its own lists and tables)
        bundle = internals.compute_exports(internals.core_kb.push_level('sandbox', []))
        bundle.theory.append(None)      # type: ignore[arg-type]
        copy = internals.copy_bundle(bundle)
        copy.theory.clear()
        copy.symbols.add('x')
        self.assertEqual(len(bundle.theory), 1)
        self.assertNotIn('x', bundle.symbols)


if __name__ == '__main__':
    unittest.main()
