import os
import tempfile
import unittest

import kurt
import kurt.kurt as core


class TestOptionalSorts(unittest.TestCase):
    def test_sparse_signatures_and_mixed_operator(self):
        result = kurt.check_text(
            'sort nat, vec\n'
            'nat n\n'
            'vec v, scale 0 2\n'
            'nat scale 1\n'
            'arity scale 2\n'
            'prop P\n'
            'arity P 1\n'
            'use P (scale n v)\n'
        )
        self.assertTrue(result.ok, result.error)

        wrong = kurt.check_text(
            'sort nat, vec\n'
            'nat n\n'
            'vec v, scale 0 2\n'
            'nat scale 1\n'
            'arity scale 2\n'
            'prop P\n'
            'arity P 1\n'
            'use P (scale v n)\n'
        )
        self.assertFalse(wrong.ok)
        self.assertIn('must have sort `nat`', wrong.error or '')

    def test_sort_property_does_not_choose_const_or_var(self):
        variable = kurt.check_text('sort nat\nnat a\nvar a\n')
        constant = kurt.check_text('sort nat\nnat a\nconst a\n')
        self.assertTrue(variable.ok, variable.error)
        self.assertTrue(constant.ok, constant.error)

    def test_bool_is_builtin_and_sort_names_are_reserved(self):
        redeclared = kurt.check_text('sort prop\n')
        self.assertFalse(redeclared.ok)
        self.assertIn('it is no sort', redeclared.error or '')

        used = kurt.check_text('sort nat\nprop P\narity P 1\nuse P nat\n')
        self.assertFalse(used.ok)
        self.assertIn('cannot be used as a term symbol', used.error or '')

        declared = kurt.check_text('sort nat\nconst nat\n')
        self.assertFalse(declared.ok)
        self.assertIn('cannot also be a constant', declared.error or '')

    def test_conflicting_position_sorts_are_rejected(self):
        result = kurt.check_text('sort nat\nnat a\nprop a\n')
        self.assertFalse(result.ok)
        self.assertIn('already has sort nat', result.error or '')

    def test_sort_listing_has_origins(self):
        result = kurt.check_text('sort nat\nnat a\nsort\nnat\n', name='typed.kurt')
        self.assertTrue(result.ok, result.error)
        self.assertIn('sort any', result.output)
        self.assertNotIn('prop', result.output)          # (`prop` declares statements: no sort)
        self.assertIn('builtin', result.output)
        self.assertIn('sort nat', result.output)
        self.assertIn('typed.kurt:1', result.output)
        self.assertIn('nat a 0', result.output)
        self.assertIn('typed.kurt:2', result.output)

    def test_sort_signatures_survive_load(self):
        with tempfile.TemporaryDirectory() as tmp:
            helper = os.path.join(tmp, 'typed.kurt')
            with open(helper, 'w') as stream:
                stream.write('sort item\nitem c\nprop P\narity P 1\nuse P c "typed"\n')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            result = session.check_text('load typed\nlist item typed\n')
            self.assertTrue(result.ok, result.error)
            self.assertIn('item c 0', result.output)

    def test_bare_sort_declaration_survives_load(self):
        with tempfile.TemporaryDirectory() as tmp:
            helper = os.path.join(tmp, 'categories.kurt')
            with open(helper, 'w') as stream:
                stream.write('sort nat\n')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            result = session.check_text('load categories\nlist sort categories\n')
            self.assertTrue(result.ok, result.error)
            self.assertIn('sort nat', result.output)
            self.assertIn('categories.kurt:1', result.output)

    def test_sort_and_symbol_names_cannot_clash_across_load(self):
        with tempfile.TemporaryDirectory() as tmp:
            sorted_file = os.path.join(tmp, 'sorted.kurt')
            symbol_file = os.path.join(tmp, 'symbol.kurt')
            with open(sorted_file, 'w') as stream:
                stream.write('sort object\nobject c\nprop P\narity P 1\nuse P c "typed"\n')
            with open(symbol_file, 'w') as stream:
                stream.write('prop object\nuse object "object-fact"\n')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            first_symbol = session.check_text('load symbol\nload sorted\n')
            first_sort = session.check_text('load sorted\nload symbol\n')
            self.assertFalse(first_symbol.ok)
            self.assertFalse(first_sort.ok)
            self.assertIn('term symbol', first_symbol.error or '')
            self.assertIn('sort here', first_sort.error or '')

    def test_untyped_kurt_is_unchanged(self):
        result = kurt.check_text('prop P\narity P 1\nuse P a\n')
        self.assertTrue(result.ok, result.error)

    def test_schema_matching_preserves_declared_sorts(self):
        source = (
            'sort nat, vec\n'
            'var n, v\n'
            'nat n\n'
            'vec v\n'
            'prop P 0\n'
            'arity P 1\n'
            'prop Q\n'
            'use (P n) implies Q "nat-only"\n'
            'use P v "vector-fact"\n'
            'Q\n'
        )
        result = kurt.check_text(source)
        self.assertFalse(result.ok)
        self.assertIn('can not derive `Q`', result.error or '')

    def test_exported_schema_matching_preserves_declared_sorts(self):
        with tempfile.TemporaryDirectory() as tmp:
            helper = os.path.join(tmp, 'nat-rule.kurt')
            with open(helper, 'w') as stream:
                stream.write(
                    'sort nat\nvar n\nnat n\nprop P 0\narity P 1\nprop Q\n'
                    'use (P n) implies Q "nat-only"\n'
                )
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            result = session.check_text(
                'sort vec\nvar v\nvec v\nload nat-rule\nuse P v "vector-fact"\nQ\n'
            )
            self.assertFalse(result.ok)
            self.assertIn('can not derive `Q`', result.error or '')

    def test_completion_includes_declared_sort(self):
        shell = core.Shell()
        self.assertTrue(shell.start_text('sort natural\nbreakpoint\n').ok)
        self.assertIn('natural', shell.completions('nat', 'nat'))

    def test_lambda_paper_typing_notation_is_sorted(self):
        good = kurt.check_text(
            'load lambda\n'
            '(extend empty base) ⊢ (at zero) : base\n'
            'empty ⊢ (abs base (at zero)) : (fun base base)\n'
            'empty ⊢ (λ x x) : (fun base base)\n'
        )
        self.assertTrue(good.ok, good.error)

        bad = kurt.check_text('load lambda\nempty ⊢ base : unit\n')
        self.assertFalse(bad.ok)
        self.assertIn('must have sort `term`', bad.error or '')

    def test_binding_operator_propagates_sort_to_bound_variable(self):
        good = kurt.check_text(
            'sort item\narity λ 2\nbinder λ\nitem λ 0 1 2\n'
            'prop P 0\narity P 1\nuse P (λ x x)\n'
        )
        self.assertTrue(good.ok, good.error)

        # (a constant of another sort is refused; one without a sort takes it, todo 34)
        bad = kurt.check_text(
            'sort item, other\narity λ 2\nbinder λ\nitem λ 0 1 2\n'
            'other c\nconst c\nprop P 0\narity P 1\nuse P (λ x c)\n'
        )
        self.assertFalse(bad.ok)
        self.assertIn('must have sort `item`', bad.error or '')

    def test_later_grammar_declaration_revalidates_sort_signature(self):
        result = kurt.check_text('sort item\nitem f 2\narity f 1\n')
        self.assertFalse(result.ok)
        self.assertIn('more than 1 arg', result.error or '')


HEAD = 'load propositional, equality, logic\n'
NUMBERS = 'sort set real\ninfix + 60 60\ninfix ∈ 25 25\nprop ∈ 0\nset ∈ 1 2\nreal + 0 1 2\n'


def check(text: str, **options) -> 'kurt.CheckResult':
    return kurt.check_text(text, **options)


class TestSubsorts(unittest.TestCase):
    # todo 34: `sort set real int` -- a DAG of sorts, a value of a subsort fits a bigger sort

    def test_a_chain_declares_the_sorts_and_the_subsorts(self):
        result = check('sort set real int, set vec\nsort\n', name='sorts.kurt')
        self.assertTrue(result.ok, result.error)
        self.assertIn('real ⊂ set, int ⊂ real, vec ⊂ set', result.output)       # (the line says so)
        self.assertIn('sort set real', result.output)                         # (`sort` lists them)
        self.assertIn('real ⊂ set, level', result.output)
        self.assertIn('int ⊂ real, level', result.output)

    def test_a_chain_may_use_known_sorts(self):
        self.assertTrue(check('sort set, real\nsort set real\n').ok)
        self.assertTrue(check('sort set real\nsort set real\n').ok)          # (known already)
        twice = check('sort set\nsort set\n')
        self.assertFalse(twice.ok)                                            # (one name alone: a new sort)
        self.assertIn('already declared', twice.error or '')

    def test_cycles_are_refused(self):
        result = check('sort set real int\nsort int set\n')
        self.assertFalse(result.ok)
        self.assertIn('would be a cycle', result.error or '')
        self.assertIn('not a subsort of itself', check('sort a a\n').error or '')

    def test_a_sort_name_as_a_symbol_gets_the_hint(self):
        result = check('sort set, real\nset real\n')
        self.assertFalse(result.ok)
        self.assertIn('a subsort is declared with `sort set real`', result.error or '')

    def test_transitive_fitting(self):
        session = core.Session()
        self.assertTrue(session.check_text('sort set real int\n').ok)
        last = session.last_kb
        assert last is not None
        self.assertTrue(last.sort_fits('int', 'set'))
        self.assertTrue(last.sort_fits('int', 'real'))
        self.assertFalse(last.sort_fits('set', 'int'))
        self.assertFalse(last.sort_fits('real', 'int'))
        self.assertTrue(core.k_sort_fits('int', 'set', last))       # (the kernel's own reading)
        self.assertFalse(core.k_sort_fits('set', 'real', last))

    def test_subsorts_cross_load_and_cycles_across_files_are_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, 'sorts.kurt'), 'w') as stream:
                stream.write('sort set real\n')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            crossed = session.check_text('load sorts\nsort\n')
            self.assertTrue(crossed.ok, crossed.error)
            self.assertIn('real ⊂ set', crossed.output)
            cycle = session.check_text('load sorts\nsort real set\n')
            self.assertFalse(cycle.ok)
            self.assertIn('cycle', cycle.error or '')


class TestFitting(unittest.TestCase):
    def test_a_value_of_a_subsort_fits_a_bigger_position(self):
        result = check(HEAD + 'sort set real\ninfix + 60 60\ninfix ∈ 25 25\nprop ∈ 0\nset ∈ 1 2\nreal + 0 1 2\n'
                       'real a, b\nuse (a + b) ∈ b\n')
        self.assertTrue(result.ok, result.error)

    def test_a_value_of_a_bigger_sort_does_not_fit(self):
        result = check(HEAD + 'sort set real\ninfix + 60 60\nreal + 0 1 2\nset s\nuse s + s = s\n')
        self.assertFalse(result.ok)
        self.assertIn('must have sort `real`', result.error or '')

    def test_a_sorted_rule_is_strict(self):
        # a rule over the numbers doesn't apply to a set, a rule over the sets applies to a number
        text = HEAD + 'sort set real\nprop P, Q\narity P 1, Q 1\nvar n, s\nreal n\nset s\nuse P n "p"\nuse Q s "q"\n'
        fine = check(text + 'real c\nP c\nQ c\n')
        self.assertTrue(fine.ok, fine.error)
        refused = check(text + 'set c\nP c\n')
        self.assertFalse(refused.ok)
        self.assertIn('can not derive', refused.error or '')

    def test_set_rules_apply_to_numbers_and_junk_is_refused(self):
        self.assertTrue(check('load natural\n3 ∈ {3}\n').ok)
        junk = check('load natural\n{1, 2} + 0 = {1, 2}\n')
        self.assertFalse(junk.ok)
        self.assertIn('TypeError', junk.error or '')
        self.assertFalse(check('load natural\nNat + 1 ∈ Nat\n').ok)


class TestDefault(unittest.TestCase):
    def test_default_needs_a_sort(self):
        result = check('default real\n')
        self.assertFalse(result.ok)
        self.assertIn('`real` is not a sort', result.error or '')
        self.assertIn('can not be the default', check('default prop\n').error or '')

    def test_default_gives_new_constants_variables_and_positions_their_sort(self):
        result = check(HEAD + 'sort real\ndefault real\ninfix ** 70 70\nconst c\nuse c ** $x = $x\ninfo c\ninfo **\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('real ** 0 1 2', result.output)
        self.assertIn('real c', result.output)
        self.assertIn('(by default)', result.output)

    def test_the_last_default_counts_from_its_line_on(self):
        result = check(HEAD + 'sort a, b\ndefault a\nconst x\nuse x = x\ndefault b\nconst y\nuse y = y\ninfo x\ninfo y\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('a x 0', result.output)
        self.assertIn('b y 0', result.output)

    def test_default_does_not_cross_load(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, 'defaulted.kurt'), 'w') as stream:
                stream.write('load propositional, equality\nsort real\ndefault real\nconst k\nuse k = k "k"\n')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            result = session.check_text('load defaulted\nconst m\nuse m = m\ninfo k\ninfo m\ndefault\n')
            self.assertTrue(result.ok, result.error)
            self.assertIn('real k 0', result.output)        # (the sort it gave crosses)
            self.assertNotIn('real m', result.output)       # (the default does not)
            self.assertIn('no default sort', result.output)


class TestInference(unittest.TestCase):
    def test_a_constant_takes_the_sort_of_its_first_sorted_use(self):
        # (a sorted rule doesn't apply to an unsorted constant: without the inference, this failed)
        result = check(HEAD + 'sort real\ninfix + 60 60\nreal + 0 1 2\nuse $a + 0 = $a\nconst x\nx + 0 = x\n'
                       'const y, z\nuse y = z\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('real x', result.output)
        self.assertIn('sort inferred', result.output)
        self.assertNotIn('real y', result.output)       # (`=` is polymorphic: no sort from it)

    def test_a_use_at_a_smaller_sort_is_a_type_error(self):
        # (the first sorted use is final, decided 2026-10-19: no narrowing)
        result = check(HEAD + NUMBERS + 'const x, A\nuse x ∈ A\nuse x + x = x\ninfo x\n')
        if not result.ok:
            self.assertIn('declare `real x` before that use', result.error or '')

    def test_a_conflicting_later_use_names_both_places(self):
        result = check(HEAD + 'sort real, vec\ninfix + 60 60\ninfix · 70 70\nreal + 0 1 2\nvec · 0 1 2\n'
                       'const x\nuse x + x = x\nuse x · x = x\n')
        self.assertFalse(result.ok)
        self.assertIn('`x` has the sort `real` (inferred at line 8), but here it is used as `vec`', result.error or '')

    def test_the_default_decides_at_an_element_not_at_a_set(self):
        # (the left of `∈`, the membership of the calculator, `builtin ∈ element`, is an element)
        result = check(HEAD + NUMBERS + 'builtin ∈ element\ndefault real\nconst x, A\nuse x ∈ A\ninfo x\ninfo A\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('real x 0', result.output)
        self.assertIn('set A 0', result.output)

    def test_a_membership_gives_no_sort(self):
        # (sorts come from declarations, the default and uses, never from a fact, todo 35)
        result = check('load natural\nconst k\nuse k ∈ Nat\ninfo k\n')
        self.assertTrue(result.ok, result.error)
        self.assertNotIn('real k 0', result.output)

    def test_a_definition_gives_its_symbol_the_sort_of_its_right_side(self):
        result = check('load natural\ndef c = {1, 2}\ninfo c\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('set c 0', result.output)
        self.assertIn('(of its definition)', result.output)
        self.assertFalse(check('load natural\ndef c = {1, 2}\nc + 0 = c\n').ok)    # (not made a number)


class TestCoreSorts(unittest.TestCase):
    # `any` (the supersort of every sort, and the sort of every symbol without one) is a sort of every
    # file (todo 35); `term` is none any more (an ordinary name, lambda.kurt declares it)

    def test_any_is_a_sort_already_term_is_none(self):
        self.assertFalse(check('sort any\n').ok)
        self.assertTrue(check('sort term\n').ok)
        self.assertTrue(check('any x\n').ok)       # (also in a file without sorts)
        self.assertFalse(check('term x\n').ok)

    def test_every_value_fits_where_any_is_required(self):
        result = check('load natural\nconst f\narity f 1\nany f 1\nuse f 3 = f {1}\n')
        self.assertTrue(result.ok, result.error)

    def test_a_value_of_sort_any_fits_no_other_sort(self):
        result = check('load natural\nany x\nuse x + 0 = x\n')
        self.assertFalse(result.ok)
        self.assertIn('must have sort `real`', result.error or '')

    def test_a_constant_without_a_sort_is_any_object_until_a_use_narrows_it(self):
        # (a fact about a sort of its own doesn't apply to it, and a use makes it a number)
        result = check('load natural\nsort foo\nfoo z\nconst P\nprop P\narity P 1\nuse ∀ z (P z)\nconst c\nP c\n')
        self.assertFalse(result.ok)
        self.assertTrue(check('load natural\nconst c\nuse c + 0 = c\nuse c ∈ Nat\n').ok)

    def test_a_polymorphic_variable_has_no_sort(self):
        # (`$$x` is a sort variable, todo 35: nothing in a rule gives it a sort)
        result = check('load natural\nconst Q\nprop Q\narity Q 1\nuse ∀ n (n + 0 = n ⇒ Q n)\n4 + 0 = 4 ⇒ Q 4\n')
        self.assertTrue(result.ok, result.error)


class TestFirstUseFinal(unittest.TestCase):
    # A constant's sort is decided by its first sorted use, and that is final (doc/kurt-spec.md §2.4, decided
    # 2026-10-19; before, a later use at a smaller sort narrowed it): no later line changes the sort of a symbol

    def test_a_later_use_at_a_smaller_sort_is_a_type_error(self):
        result = check('load natural\nconst x, A\nuse x ⊂ A\ninfo x\nuse x + 0 = x\n')
        self.assertFalse(result.ok)
        self.assertIn('`x` has the sort `set` (inferred at line 3), but here it is used as `real`', result.error or '')
        self.assertIn('declare `real x` before that use', result.error or '')

    def test_a_declaration_first_makes_it_smaller(self):
        result = check('load natural\nconst A\nreal x\nuse x ⊂ A\nuse x + 0 = x\nx ⊂ A\n')
        self.assertTrue(result.ok, result.error)

    def test_no_sort_before_the_first_sorted_use(self):
        # (`z = z`: `=` gives no sort; `z + 0` is the first sorted use)
        result = check('load natural\nconst z\nuse z = z\nuse z + 0 = z\ninfo z\n')
        self.assertTrue(result.ok, result.error)
        self.assertIn('real z 0', result.output)

    def test_a_fact_gives_no_sort_the_hint_says_so(self):
        result = check('load natural\nset b\nuse b ∈ Nat\nuse b + 1 = 1 + b\n')
        self.assertFalse(result.ok)
        self.assertIn('a fact `b ∈ Nat` gives no sort; declare `real b`', result.error or '')

    def test_not_a_sort_of_a_loaded_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, 'lib.kurt'), 'w') as stream:
                stream.write('load natural\nconst g, A\nuse g ⊂ A\n')
            session = kurt.Session(kurt.RunConfig(paths=(tmp,)))
            result = session.check_text('load lib\nuse g + 0 = g\n')
        self.assertFalse(result.ok)
        self.assertIn('`g` has the sort `set` (inferred at', result.error or '')
        self.assertIn('but here it is used as `real`', result.error or '')

    def test_not_a_declared_sort(self):
        result = check('load natural\nconst A\nset s\nuse s ⊂ A\nuse s + 0 = s\n')
        self.assertFalse(result.ok)
        self.assertIn('must have sort `real`', result.error or '')

    def test_not_a_witness(self):
        # (`pick w` from `∃ x (x ∈ A)`: a use as a number would be a claim about `w` that the existential doesn't make)
        result = check('load natural\nconst A\nuse ∃ y (y ∈ A)\npick w with w ∈ A\n    use w + 0 = w\n')
        self.assertFalse(result.ok)
        self.assertIn('sort', result.error or '')

    def test_a_polymorphic_rule_gives_no_sort(self):
        # (logic.kurt's rules are over `$$x`: using one for a constant doesn't give the constant a sort)
        result = check('load natural\nconst Q, c\nprop Q\narity Q 1\nuse ∀ n (n + 0 = n ⇒ Q n)\nuse ∀ x (Q x)\nuse Q c\ninfo c\n')
        self.assertTrue(result.ok, result.error)
        self.assertNotIn('real c', result.output)
        self.assertNotIn('set c', result.output)


class TestBlocksKeepTheirSorts(unittest.TestCase):
    TEXT = ('load natural\nprop R\narity R 1\nconst R\nuse ∀ $n ($n + 0 = $n ⇒ R $n)\n'
            'let c\n    c + 0 = c\n    R c\n')

    def test_a_let_constant_of_a_sort_gives_a_binder_of_that_sort(self):
        self.assertTrue(check(self.TEXT + 'R 7\n').ok)
        self.assertFalse(check(self.TEXT + 'R {1}\n').ok)
        self.assertFalse(check(self.TEXT + '∀ c (R c)\n').ok)     # (over everything, written again)

    def test_the_kernel_checks_the_sorts_of_a_block_result(self):
        # with the sorts of the block's constants dropped from the result, the kernel refuses it
        from unittest import mock
        with mock.patch.object(core, 'block_result_sorts', lambda block: {}):
            result = check(self.TEXT)
        self.assertFalse(result.ok)
        self.assertIn('the result is about everything', result.error or '')

    def test_a_witness_has_the_sort_of_the_bound_variable(self):
        result = check('load natural\nconst A\nuse ∃ x (x ∈ A)\npick w with w ∈ A\n    w + 0 = w\n')
        self.assertFalse(result.ok)
        self.assertIn('must have sort `real`', result.error or '')


class TestKernelSorts(unittest.TestCase):
    def kb(self):
        session = core.Session()
        self.assertTrue(session.check_text('load natural\n').ok)
        return session

    def test_the_kernel_reads_subsorts_itself(self):
        session = self.kb()
        kb = session.last_kb
        assert kb is not None
        three = core.Token('INT', 3)
        self.assertTrue(core.k_has_sort(three, 'real', kb))
        self.assertTrue(core.k_has_sort(three, 'set', kb))
        self.assertTrue(core.k_has_sort(core.Token('SYMBOL', 'Nat'), 'set', kb))
        self.assertFalse(core.k_has_sort(core.Token('SYMBOL', 'Nat'), 'real', kb))

    def test_a_bound_variable_in_a_body_is_not_relativized(self):
        # "extensionality" `∀ $c ($c ∈ $a ⇔ $c ∈ $b)` can't be used for a binder over the numbers:
        # the kernel refuses such an instance by itself
        session = self.kb()
        kb = session.last_kb
        assert kb is not None
        with session._active():
            rule = next(f for f in kb.all_theory() if f.label == 'extensionality')
            expr = rule.simplified_expr
            binders = core.k_binder_variables(expr, kb)
            self.assertTrue(binders)
            self.assertFalse(binders & core.k_parametric_binders(expr, kb))
            forall_elim = next(f for f in kb.all_theory() if f.label == 'forall-elim')
            self.assertTrue(core.k_binder_variables(forall_elim.simplified_expr, kb)
                            <= core.k_parametric_binders(forall_elim.simplified_expr, kb))
            bound = next(iter(binders))
            fresh = core.new_var_name()
            core.run_state.internal_variable_sorts[fresh] = frozenset({'real'})
            with self.assertRaises(core.KernelReject):
                core.k_instance(expr, {bound: core.Token('SYMBOL', fresh)}, {}, kb, core.k_parametric_binders(expr, kb))


class TestElements(unittest.TestCase):
    RULE = HEAD + 'sort set real\n{}infix ∈ 25 25\nprop ∈ 0\nset ∈ 1 2\nprop P\narity P 1\nvar s\nset s\nuse P s\nconst k\nuse k = k\nP k\n'

    def test_a_value_without_a_sort_is_no_set(self):
        # design B: no sort is the sort of all objects, `set` a restriction (no `everything` any more)
        self.assertFalse(check(self.RULE.format('')).ok)           # (an unsorted `k` is no set)
        self.assertFalse(check(self.RULE.format('everything set\n')).ok)   # (the keyword is gone)

    def test_a_declaration_of_the_sort_of_a_sets_elements_is_gone(self):
        # (`real ∈ Odd`, todo 34, is no declaration any more: a fact or a declaration gives no sort, todo 35)
        result = check(HEAD + NUMBERS + 'builtin ∈ element\nconst Odd\nreal ∈ Odd\n')
        self.assertFalse(result.ok)
        result = check(HEAD + NUMBERS + 'builtin ∈ element\nconst Odd\nconst x\nuse x ∈ Odd\ninfo x\n')
        self.assertTrue(result.ok, result.error)
        self.assertNotIn('real x 0', result.output)


class TestInhabitedSorts(unittest.TestCase):
    # all sorts are inhabited (spec §2.2): a file that declares a sort and names no object of it
    # assumes one -- a warning at its end (todo 67, 2026-10-23)
    def warnings(self, text):
        import contextlib, io
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            result = kurt.check_text(text, name='inhabited.kurt')
        self.assertTrue(result.ok, result.error)
        return [line for line in err.getvalue().splitlines() if line.startswith('Warning: the sort')]

    def test_a_sort_without_a_constant_is_warned_about(self):
        found = self.warnings('load logic, equality\nsort vec, nat\nnat zero\nvar v\nvec v\nuse ∀ v (v = v)\n')
        self.assertEqual(len(found), 1)
        self.assertIn('the sort `vec` (declared at inhabited.kurt:2) has no constant', found[0])

    def test_a_constant_of_a_subsort_inhabits_the_sort(self):
        self.assertEqual(self.warnings('load natural\nsort big small\nsmall s\n'), [])

    def test_a_theory_of_kurt_checked_on_its_own_is_not_warned_about(self):
        # set.kurt declares `real`, number.kurt names its objects: no warning when set.kurt
        # itself is the file checked (it came in every run of the theories as main files)
        import contextlib, io
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            result = kurt.check_file(str(core.packaged_theory_file('set.kurt')))
        self.assertTrue(result.ok, result.error)
        self.assertNotIn('Warning: the sort', err.getvalue())

    def test_the_sorts_of_a_loaded_theory_are_not_the_files(self):
        self.assertEqual(self.warnings('load natural\nconst a\nuse a = a\n'), [])


if __name__ == '__main__':
    unittest.main()
