import ast
import copy
import unittest

import kurt.kurt as kurt
from kurt.kurt import Token
from tests.utils import PROJECT_ROOT

# the kernel (`kernel_verify`, `kernel_verify_block`, `k_*`) must not share code with the search,
# where the bugs were (doc/kurt-soundness.md §9): it may call only the module functions below --
# each one simple, or the meaning of a declaration itself. A new one needs a reason here.
ALLOWED = {
    # the meaning of `flat`, `sym` and `calc`: trusted semantics, not search
    'normalize_expr', 'calculate_normalized', 'numeric_comparison_holds',
    # plain predicates and helpers on expressions
    'is_forall', 'is_iff', 'is_implication', 'is_op_expr', 'is_sub', 'is_relation', 'is_bool_var_token',
    'get_token_set', 'deepcopy_expr', 'expr_str', 'new_var_name', 'new_bool_var_name',
    # the read-only view of the knowledge base for one check
    'k_env',
}
ONLY_IN_BLOCK: set[str] = set()
SEARCH = {'equal_expr', 'unify_exprs_with_patterns', 'match_against_sub', 'impl_elim', 'derive_expr',
          'trigger_sub', 'apply_subst', 'capture_avoiding_replace', 'rename_all_vars', 'match_all_theory',
          'unpack_condition', 'binder_reading', 'binder_reading_changes'}


class TestKernelBoundary(unittest.TestCase):
    def calls(self) -> dict[str, set[str]]:
        tree = ast.parse((PROJECT_ROOT / 'src' / 'kurt' / 'kurt.py').read_text(encoding='utf-8'))
        functions = {n.name: n for n in tree.body if isinstance(n, ast.FunctionDef)}
        kernel = {n for n in functions if (n.startswith('k_') or n.startswith('kernel_verify')) and n != 'k_env'}
        calls: dict[str, set[str]] = {}
        for k in kernel:
            for node in ast.walk(functions[k]):
                if isinstance(node, ast.Call) and isinstance(node.func, ast.Name):
                    name = node.func.id
                    if name in functions and name not in kernel:
                        calls.setdefault(name, set()).add(k)
        return calls

    def test_the_kernel_calls_no_search_code(self):
        calls = self.calls()
        self.assertFalse(set(calls) & SEARCH, {n: calls[n] for n in set(calls) & SEARCH})
        self.assertFalse(set(calls) - ALLOWED, {n: calls[n] for n in set(calls) - ALLOWED})
        for name in ONLY_IN_BLOCK & set(calls):
            self.assertEqual(calls[name], {'kernel_verify_block'}, name)


S = lambda v: Token('SYMBOL', v)

class TestKernelReading(unittest.TestCase):
    def setUp(self):
        import io, contextlib
        self.kb = copy.deepcopy(kurt.initial_kb)
        with contextlib.redirect_stdout(io.StringIO()):
            self.kb = kurt.load_file('set', self.kb)
        self.kb.add_const('A')

    def test_binder_reading(self):
        kb = self.kb
        self.assertEqual(kurt.k_bound(S('$$1'), kb), '$$1')
        self.assertEqual(kurt.k_bound([S('in'), S('$$1'), S('A')], kb), '$$1')           # one variable
        self.assertEqual(kurt.k_bound([S('in'), S('$$1'), S('$$2')], kb), '$$1')         # the left one
        self.assertEqual(kurt.k_bound([S('in'), S('x'), S('A')], kb), 'x')               # a new name
        with self.assertRaises(kurt.KernelReject):
            kurt.k_bound([S('in'), S('A'), S('A')], kb)                                  # nothing to bind

    def test_alpha_equivalence(self):
        kb = self.kb
        P = lambda x: [S('in'), S(x), S('A')]
        forall = lambda x, body: [S('forall'), S(x), body]
        self.assertTrue(kurt.k_equal(forall('$$1', P('$$1')), forall('$$2', P('$$2')), kb))
        self.assertFalse(kurt.k_equal(forall('$$1', P('$$1')), forall('$$2', P('$$1')), kb))   # free vs bound
        self.assertTrue(kurt.k_equal([S('='), S('a'), S('b')], [S('='), S('b'), S('a')], kb))  # `=` either way
        self.assertFalse(kurt.k_equal([S('in'), S('a'), S('b')], [S('in'), S('b'), S('a')], kb))


if __name__ == '__main__':
    unittest.main()
