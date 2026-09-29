import contextlib
import copy
import io
import os
import tempfile
import unittest

import kurt.kurt as kurt

# what crosses the boundary of a loaded file (`ExportBundle`, codex-suggestions.md): the
# declarations a labelled, non-`local` fact needs -- and nothing else, not even a new field of
# `KnowledgeBase` that nobody thought of

# for each kind of declaration: the declaration of `S` and a fact that uses it (`S` is replaced
# by `X` for the exported fact, and by `Y` for an unlabelled one), and how to see it after `load`
CASES = {
    'infix':    ('infix S 50 50', 'use a S a',          lambda kb, s: kb.is_infix(s)),
    'prefix':   ('prefix S 80',   'use S a',            lambda kb, s: kb.is_prefix(s)),
    'postfix':  ('postfix S 80',  'use a S',            lambda kb, s: kb.is_postfix(s)),
    'arity':    ('arity S 1',     'use S a',            lambda kb, s: kb.get_arity(s) == 1),
    'bindop':   ('arity S 2\nbindop S', 'use S $v a',   lambda kb, s: kb.is_bindop(s)),
    'flat':     ('infix S 50 50\nflat S', 'use a S a',  lambda kb, s: kb.is_flat(s)),
    'sym':      ('infix S 50 50\nsym S', 'use a S a',   lambda kb, s: kb.is_sym(s)),
    'bool':     ('bool S',        'use S',              lambda kb, s: len(kb.bool_sig(s)) > 0),
    'calc':     ('infix S 50 50\ncalc S add', 'use P (1 S 1)', lambda kb, s: 'add' in kb.get_calc_ops(s)),
    'alias':    ('const cS\nalias S cS', 'use P cS',    lambda kb, s: kb.get_alias(s) == f'c{s}'),
    'brackets': ('brackets Sl Sr', 'use P (Sl a Sr)',   lambda kb, s: kb.is_bracket(f'{s}l')),
}
PRELUDE = 'bool P\narity P 1\nconst a\nuse P a "p"\n'


def load(files: dict[str, str], main: str) -> kurt.KnowledgeBase:
    with tempfile.TemporaryDirectory() as tmp:
        for name, text in files.items():
            with open(os.path.join(tmp, name), 'w') as fh:
                fh.write(text)
        with contextlib.redirect_stdout(io.StringIO()):
            return kurt.load_file(os.path.join(tmp, main), copy.deepcopy(kurt.initial_kb), mainstream=False)


class TestExportBundle(unittest.TestCase):
    def test_each_declaration_crosses_only_when_needed(self):
        for kind, (decl, fact, seen) in CASES.items():
            with self.subTest(kind=kind):
                helper = PRELUDE
                for name, label in (('X', ' "x"'), ('Y', '')):
                    helper += decl.replace('S', name) + '\n' + fact.replace('S', name) + label + '\n'
                kb = load({'helper.kurt': helper, 'main.kurt': 'load helper\n'}, 'main.kurt')
                self.assertTrue(seen(kb, 'X'), f'`{kind}` of X, needed by an exported fact, got lost')
                self.assertFalse(seen(kb, 'Y'), f'`{kind}` of Y, only in an unlabelled fact, crossed')

    def test_a_new_field_stays_in_the_file(self):
        parent = copy.deepcopy(kurt.initial_kb)
        child = parent.push_level('sandbox', [])
        child.some_new_bookkeeping = ['private']
        child.mode_args.append(kurt.Token('SYMBOL', 'private'))
        child.merge_and_pop()
        self.assertFalse(hasattr(parent, 'some_new_bookkeeping'))
        self.assertEqual(parent.mode_args, [])

    def test_the_bundle_shares_nothing_with_the_file(self):
        kb = load({'helper.kurt': PRELUDE + 'calc on\n'}, 'helper.kurt')      # (a top level: nothing to compare)
        child = kb.push_level('sandbox', [])
        child.add_const('b')
        child.theory_append(kurt.Formula(child, kurt.Token('SYMBOL', 'b'), 'b', '1', 'f', 'b-label', '', ''))
        child.calc_ops['b'] = ['add']
        bundle = kurt.compute_exports(child)
        bundle.calc_ops['b'].append('multiply')
        bundle.theory.clear()
        self.assertEqual(child.calc_ops['b'], ['add'])
        self.assertEqual(len(child.theory), 1)

    def test_loading_twice_changes_nothing(self):
        files = {'helper.kurt': PRELUDE, 'main.kurt': 'load helper\nload helper\n', 'once.kurt': 'load helper\n'}
        twice, once = load(files, 'main.kurt'), load(files, 'once.kurt')
        self.assertEqual(len(twice.theory), len(once.theory))


if __name__ == '__main__':
    unittest.main()
