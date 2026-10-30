import ast
import contextlib
import copy
import inspect
import io
import unittest
from collections.abc import Iterator

import kurt.kurt as kurt

# the kernel sees a knowledge base only through `KernelEnv`: read-only, only the lookups it needs
# (the members of `KbReader`), each answer fixed for the whole check

SYMBOLS = ['in', '∈', '=', 'forall', 'and', 'not', 'x', '$x', '%A', 'Nat', '+', '⊂', 'true', 'zzz']
ROLES = ['equality', 'universal', 'existential', 'equivalence', 'disjunction', 'negation', 'falsum', 'nothing']
TOKEN = kurt.Token('SYMBOL', 'x')
EXPRESSIONS = [TOKEN, kurt.Token('INT', 1), [kurt.Token('SYMBOL', 'forall'), TOKEN, TOKEN]]     # (a list is not hashable)

# the arguments of every method of `KbReader`: a new member needs a line here (test_every_method_is_compared)
SAMPLES = {
    'is_var': [(s,) for s in SYMBOLS], 'is_bool': [(s,) for s in SYMBOLS], 'bool_sig': [(s,) for s in SYMBOLS],
    'variable_sorts': [(s,) for s in SYMBOLS], 'pos_sort': [(s, i) for s in SYMBOLS for i in (0, 1, 2)],
    'pos_sorts': [(s, i) for s in SYMBOLS for i in (0, 1, 2)],
    'all_subsorts': [()], 'generalized_sorts': [(s,) for s in SYMBOLS], 'binder_sorts': [(e,) for e in EXPRESSIONS],
    'is_binder': [(s,) for s in SYMBOLS], 'is_const': [(s,) for s in SYMBOLS], 'is_known': [(s,) for s in SYMBOLS],
    'is_used': [(s,) for s in SYMBOLS], 'is_fixed_var': [(s,) for s in SYMBOLS],
    'is_vocabulary_symbol': [(s,) for s in SYMBOLS], 'get_arity': [(s,) for s in SYMBOLS],
    'is_flat': [(s,) for s in SYMBOLS], 'is_sym': [(s,) for s in SYMBOLS], 'all_flat': [()],
    'get_builtins': [(s,) for s in SYMBOLS], 'has_role': [(s, r) for s in SYMBOLS for r in ROLES],
    'role_symbol': [(r,) for r in ROLES], 'calculate': [(e,) for e in EXPRESSIONS],
    'is_operator': [(s,) for s in SYMBOLS], 'is_infix': [(s,) for s in SYMBOLS], 'is_prefix': [(s,) for s in SYMBOLS],
    'is_postfix': [(s,) for s in SYMBOLS], 'is_bracket_placeholder': [(s,) for s in SYMBOLS],
    'all_theory': [()],
}


def members() -> set[str]:
    return {name for name in vars(kurt.KbReader) if not name.startswith('_')}


def methods() -> set[str]:
    return {name for name in members() if not isinstance(vars(kurt.KbReader)[name], property)}


def normalized(value):
    # what an answer is, whether it is the live answer or a snapshot of it
    if isinstance(value, (Iterator, list, tuple)):
        return list(value)
    if isinstance(value, (set, frozenset)):
        return frozenset(value)
    return value


def outcome(call):
    try:
        return 'answer', normalized(call())
    except Exception as e:                      # (the same exception, whichever of the two is asked)
        return 'raises', type(e).__name__


class TestKernelEnv(unittest.TestCase):
    def setUp(self):
        self.kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            self.kb = kurt.load_file('set', self.kb)

    def test_read_only(self):
        env = kurt.KernelEnv(self.kb)
        with self.assertRaises(AttributeError):
            setattr(env, 'format', 'sexpr')
        with self.assertRaises(AttributeError):
            getattr(env, 'add_const')                      # not a lookup the kernel may use
        with self.assertRaises(AttributeError):
            getattr(env, 'theory_append')

    def test_answers_stay_fixed(self):
        env = kurt.KernelEnv(self.kb)
        self.assertFalse(env.is_const('zzz'))
        self.kb.add_const('zzz')                      # a change during the check isn't seen
        self.assertFalse(env.is_const('zzz'))
        self.assertTrue(kurt.KernelEnv(self.kb).is_const('zzz'))
        facts = list(env.all_theory())
        self.kb.add_const('yyy')
        self.assertEqual(len(list(env.all_theory())), len(facts))
        sig = env.bool_sig('in')
        assert isinstance(sig, list)
        sig.append(99)                               # a copy: the next answer is the same
        self.assertEqual(env.bool_sig('in'), self.kb.bool_sig('in'))

    def test_what_is_handed_out_is_a_snapshot(self):
        env = kurt.KernelEnv(self.kb)
        self.assertIsNot(env.theory, env.theory)             # a list: a new one each time
        self.assertEqual(env.theory, self.kb.theory)
        self.assertIsInstance(env.const, frozenset)           # a set: frozen
        self.assertIsInstance(env.variable_sorts('x'), frozenset)
        self.assertIsInstance(env.bool_sig('in'), list)
        first = env.all_theory()                              # a generator: a new iterator over what it gave
        self.assertIsInstance(first, Iterator)
        self.assertEqual(list(first), list(env.all_theory()))

    def test_the_protocol_lists_exactly_the_members(self):
        # `KbReader` is what the type checker lets the kernel do with a knowledge base: the same
        # members as `KernelEnv` has, no more (a member added to one must be added to the other)
        public = {name for name in vars(kurt.KernelEnv) if not name.startswith('_')}
        self.assertEqual(members(), public)

    def test_a_knowledge_base_has_every_member(self):
        # so the search can pass a `KnowledgeBase` where the kernel takes a `KbReader`
        for name in members():
            self.assertTrue(hasattr(self.kb, name), name)

    def test_every_method_is_compared(self):
        self.assertEqual(set(SAMPLES), methods())

    def test_the_environment_answers_as_the_knowledge_base_does(self):
        env = kurt.KernelEnv(self.kb)
        for name, arguments in SAMPLES.items():
            for args in arguments:
                with self.subTest(name=name, args=args):
                    live = outcome(lambda: getattr(self.kb, name)(*args))
                    self.assertEqual(outcome(lambda: getattr(env, name)(*args)), live)
                    self.assertEqual(outcome(lambda: getattr(env, name)(*args)), live)      # (and when remembered)
        for name in members() - methods():
            with self.subTest(name=name):
                self.assertEqual(normalized(getattr(env, name)), normalized(getattr(self.kb, name)))

    def test_every_member_forwards_to_its_own(self):
        # the source of a member: `return self._call('NAME', self._kb.NAME, ARGUMENTS)` (or `_list`, `_frozen`,
        # `_value` for a value), with the name of the member and the arguments it was given -- no member
        # reads another one
        tree = ast.parse(inspect.getsource(kurt.KernelEnv))
        forwarders = {n.name: n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and not n.name.startswith('_')}
        self.assertEqual(set(forwarders), members())
        for name, function in forwarders.items():
            with self.subTest(name=name):
                self.assertEqual(len(function.body), 1)
                result = function.body[0]
                assert isinstance(result, ast.Return) and isinstance(result.value, ast.Call)
                call = result.value
                assert isinstance(call.func, ast.Attribute) and isinstance(call.func.value, ast.Name)
                self.assertEqual(call.func.value.id, 'self')
                expected = '_call' if name in methods() else None
                if expected:
                    self.assertEqual(call.func.attr, '_call')
                else:
                    self.assertIn(call.func.attr, ('_list', '_frozen', '_value'))
                key, member, *given = call.args
                assert isinstance(key, ast.Constant) and isinstance(member, ast.Attribute)
                self.assertEqual(key.value, name)
                self.assertEqual(member.attr, name)
                assert isinstance(member.value, ast.Attribute) and isinstance(member.value.value, ast.Name)
                self.assertEqual((member.value.value.id, member.value.attr), ('self', '_kb'))
                parameters = [a.arg for a in function.args.args][1:]
                self.assertEqual([a.id for a in given if isinstance(a, ast.Name)], parameters)
                self.assertEqual(len(given), len(parameters))


if __name__ == '__main__':
    unittest.main()
