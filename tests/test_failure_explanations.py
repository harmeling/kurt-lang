import io
import json
import unittest
import unittest.mock

import kurt
import kurt.kurt as internals


class TestFailureExplanations(unittest.TestCase):
    def test_missing_premise_is_structured_and_rendered(self):
        result = kurt.check_text('prop A, B\nuse A implies B "mp"\nB\n')
        self.assertFalse(result.ok)
        self.assertEqual(result.failure, {
            'kind': 'not-derived',
            'goal': 'B',
            'summary': 'no one-step derivation was found',
            'candidates': [{
                'rule': 'mp',
                'location': 'line 2',
                'missing': ['A'],
                'matched': [],
            }],
            'counterexample': {'assignment': {'A': False, 'B': False}},
        })
        self.assertIn('`mp` (line 2): missing `A`', result.error or '')
        self.assertEqual(result.events[-1]['failure'], result.failure)
        self.assertEqual(json.loads(result.to_json())['failure'], result.failure)

    def test_reports_present_and_missing_parts_of_a_premise(self):
        result = kurt.check_text(
            'load propositional\nprop A, B, C\nuse A and B implies C "both"\nuse A\nC\n')
        candidate = result.failure['candidates'][0]
        self.assertEqual((candidate['rule'], candidate['missing']), ('both', ['B']))
        self.assertEqual(candidate['matched'], ['line 4'])

    def test_success_has_no_failure_explanation(self):
        result = kurt.check_text('prop A, B\nuse A implies B\nuse A\nB\n')
        self.assertTrue(result.ok)
        self.assertIsNone(result.failure)

    def test_number_of_suggestions_is_bounded(self):
        result = kurt.check_text(
            'prop A, B\n'
            'use A implies B "one"\nuse A implies B "two"\n'
            'use A implies B "three"\nuse A implies B "four"\nB\n')
        self.assertLessEqual(len(result.failure['candidates']), 3)

    def test_failed_goal_uses_source_variable_names(self):
        result = kurt.check_text('var x\nconst P\nP x\n')
        self.assertFalse(result.ok)
        self.assertEqual(result.failure['goal'], 'P x')
        self.assertIn('can not derive `P x`', result.error or '')
        self.assertNotIn('$$', result.error or '')
        self.assertNotIn('%%', result.error or '')



class TestMissingConditions(unittest.TestCase):
    def test_the_condition_of_a_fact_is_named_and_the_catch_alls_come_last(self):
        # since 2026-10-12: before, the list had "bottom-elim" and "forall-elim" (and for an
        # `=` "extensionality") but not the missing condition of the fact `∀ y ∈ A (y ∈ B)`
        result = kurt.check_text('load set\nconst A, B, x\nuse ∀ y ∈ A (y ∈ B)\nx ∈ B\n')
        self.assertFalse(result.ok)
        self.assertIn('`line 3`: missing `x ∈ A`', result.error)
        self.assertNotIn('bottom-elim', result.error)
        self.assertNotIn('extensionality', result.error)


class TestSortMismatches(unittest.TestCase):
    # todo 38: a sorted schema variable that can't match an unsorted value used to fail completely
    # silently (the rule simply absent from the candidates); `failure_explanation` now retries with
    # sorts ignored (`ignoring_sorts`) and names exactly which variable/sort/value was the problem --
    # a diagnostic only, never a change to what the live search accepts

    TEXT = ('sort obj\nconst a\nvar x\nobj x\n'
            'arity P 1\narity Q 1\n'
            'use (Q x) implies (P x) "p-rule"\nuse Q x "q-always"\nP a\n')

    def test_names_the_rule_variable_sort_and_value(self):
        result = kurt.check_text(self.TEXT)
        self.assertFalse(result.ok)
        self.assertEqual(result.failure['sort_mismatches'], [{
            'rule': 'p-rule',
            'location': 'line 7',
            'violations': ['`x` needs sort `obj`, but `a` has no declared sort'],
        }])
        self.assertEqual(result.failure['candidates'], [])
        self.assertIn('`p-rule` (line 7): `x` needs sort `obj`, but `a` has no declared sort', result.error)
        self.assertIn("a rule's conclusion would match except for a declared sort", result.error)

    def test_never_fires_when_an_ordinary_candidate_exists(self):
        # a genuine missing-premise case is unaffected: no `sort_mismatches` key at all
        result = kurt.check_text('prop A, B\nuse A implies B "mp"\nB\n')
        self.assertFalse(result.ok)
        self.assertNotIn('sort_mismatches', result.failure)

    def test_a_structurally_impossible_rule_gets_neither(self):
        # `a` and `b` are both unsorted, incompatible constants -- a genuine "no rule at all"
        # case, not a sort issue, so neither `candidates` nor `sort_mismatches` has anything
        result = kurt.check_text('const a, b\narity P 1\nuse P a "p-of-a"\nP b\n')
        self.assertFalse(result.ok)
        self.assertEqual(result.failure['candidates'], [])
        self.assertNotIn('sort_mismatches', result.failure)
        self.assertIn('no rule with a matching conclusion was found', result.error)


COUNTEREXAMPLE_LINE = ('a counterexample: with `A` false, `B` false and `C` true, every fact holds but the claim '
                       "doesn't -- it does not follow from these facts")

def lsp_notifications(output: io.BytesIO) -> list[dict]:
    # the messages a `LanguageServer` wrote to `output`
    data = output.getvalue()
    messages = []
    while data:
        header, _, rest = data.partition(b'\r\n\r\n')
        length = int(header.decode('ascii').split(':')[1])
        messages.append(json.loads(rest[:length]))
        data = rest[length:]
    return messages


class TestCounterexamples(unittest.TestCase):
    # since 2026-10-16: a propositional claim that doesn't follow from the facts gets a truth-table
    # counterexample; a claim that follows (in more steps), a claim or fact outside the truth table's
    # reach, and a table beyond the bounds get no word about it

    def test_a_propositional_claim_gets_a_counterexample(self):
        result = kurt.check_text('load propositional\nprop A, B, C\nuse A ⇒ B\nuse A ∨ C\nB\n')
        self.assertFalse(result.ok)
        self.assertEqual(result.failure['counterexample'], {'assignment': {'A': False, 'B': False, 'C': True}})
        self.assertIn(COUNTEREXAMPLE_LINE, result.error)
        self.assertIn('`line 3`: missing `A`', result.error)       # (the missing premises are still there)

    def test_a_claim_that_follows_in_more_steps_gets_none(self):
        # `C` follows from `A`, `A ⇒ B`, `B ⇒ C` -- not in one step, but in every row of the truth
        # table: nothing must suggest that it is false
        result = kurt.check_text('load propositional\nprop A, B, C\nuse A ⇒ B\nuse B ⇒ C\nuse A\nC\n')
        self.assertFalse(result.ok)
        self.assertNotIn('counterexample', result.failure)
        self.assertNotIn('counterexample', result.error)
        self.assertIn('missing `B`', result.error)
        # the same from inside a block: `A` from `A ∨ B` and `¬B` needs or-elim, it holds in every row
        result = kurt.check_text('load propositional\nprop A, B, C\nuse A ∨ B\nuse ¬B\nshow C ⇒ A\nproof\n    assume C\n        A\nqed\n')
        self.assertFalse(result.ok)
        self.assertNotIn('counterexample', result.error)

    def test_false_from_consistent_facts_and_opaque_atoms(self):
        result = kurt.check_text('load propositional\nprop A, B\nuse A\nuse A ⇒ B\nfalse\n')
        self.assertEqual(result.failure['counterexample'], {'assignment': {'A': True, 'B': True}})
        # `false` from nothing: the empty assignment is the counterexample (an IndexError, 2026-10-16)
        result = kurt.check_text('load propositional\nfalse\n')
        self.assertEqual(result.failure['counterexample'], {'assignment': {}})
        self.assertIn("a counterexample: every fact holds but the claim doesn't", result.error)
        # a statement about objects is an atom: `P a` says nothing about `P b`
        result = kurt.check_text('load propositional\nconst P, a, b\nuse P a\nP b\n')
        self.assertEqual(result.failure['counterexample'], {'assignment': {'P a': True, 'P b': False}})
        self.assertIn('with `P a` true and `P b` false', result.error)
        # a `def` is a fact about its symbol
        result = kurt.check_text('load propositional\nprop A, B\ndef C iff A ∧ B\nuse A\nC\n')
        self.assertEqual(result.failure['counterexample'], {'assignment': {'A': True, 'B': False, 'C': False}})

    def test_first_order_facts_and_schematic_claims_get_none(self):
        # a fact with a quantifier or an object variable may say something about the atoms that a
        # truth table can't see: no counterexample, whatever the atoms
        for text in ('load set\nconst A, B, x\nuse ∀ y ∈ A (y ∈ B)\nx ∈ B\n',
                     'load logic\nprop A, B\nuse A\nB\n',
                     'load propositional\nconst P\nvar x\nuse P x\nprop A\nA\n',
                     'load propositional\nprop A\nuse A\n%X ∧ A\n',                  # (a claim with a variable)
                     'load propositional\nprop A, B\nuse A\nA ⇐ B\n'):               # (`⇐` has no truth table of its own)
            result = kurt.check_text(text)
            self.assertFalse(result.ok, text)
            self.assertNotIn('counterexample', result.failure or {}, text)
            self.assertNotIn('counterexample', result.error, text)

    def test_the_bounds(self):
        def chain(n: int) -> str:
            atoms = ', '.join(f'A{i}' for i in range(n))
            return f'load propositional\nprop {atoms}\n' + ''.join(f'use A{i} ∨ A{i + 1}\n' for i in range(n - 1)) + 'A0\n'
        self.assertIn('counterexample', kurt.check_text(chain(internals.COUNTEREXAMPLE_ATOMS)).failure)
        self.assertNotIn('counterexample', kurt.check_text(chain(internals.COUNTEREXAMPLE_ATOMS + 1)).failure)
        # the time: the one row that refutes `Z` (every `A` true) is the 256th tried; with no time
        # left, the table stops at its first look at the clock
        text = 'load propositional\nprop Z, ' + ', '.join(f'A{i}' for i in range(8)) + '\n' + ''.join(f'use A{i}\n' for i in range(8)) + 'Z\n'
        self.assertIn('counterexample', kurt.check_text(text).failure)
        with unittest.mock.patch.object(internals, 'COUNTEREXAMPLE_SECONDS', -1.0):
            self.assertNotIn('counterexample', kurt.check_text(text).failure)

    def test_the_json_and_lsp_forms(self):
        text = 'load propositional\nprop A, B, C\nuse A ⇒ B\nuse A ∨ C\nB\n'
        result = kurt.check_text(text)
        expected = {'assignment': {'A': False, 'B': False, 'C': True}}
        self.assertEqual(json.loads(result.to_json())['failure']['counterexample'], expected)
        self.assertEqual(result.events[-1]['failure']['counterexample'], expected)
        self.assertEqual(result.errors[0]['failure']['counterexample'], expected)
        output = io.BytesIO()
        server = internals.LanguageServer(io.BytesIO(), output)
        uri = 'file:///tmp/counterexample.kurt'
        server.texts[uri] = text
        server.check(uri)
        published = [m for m in lsp_notifications(output) if m.get('method') == 'textDocument/publishDiagnostics']
        diagnostic = published[-1]['params']['diagnostics'][0]
        self.assertEqual(diagnostic['data']['failure']['counterexample'], expected)
        self.assertIn(COUNTEREXAMPLE_LINE, diagnostic['message'])

    def test_never_runs_for_an_accepted_line_and_never_changes_the_error(self):
        # the check is a diagnostic of a line that failed: an accepted line never sees it, and a
        # failure of the check itself leaves the error as it was
        with unittest.mock.patch.object(internals, 'propositional_counterexample',
                                        side_effect=AssertionError('ran for an accepted line')) as check:
            result = kurt.check_text('load propositional\nprop A, B, C\nuse A ∨ B\nuse ¬B\nuse A ⇒ C\nshow C\nproof\n    case A\n        C\n    case B\n        false\n        C\nqed\n')
            self.assertTrue(result.ok, result.error)
            check.assert_not_called()
        with unittest.mock.patch.object(internals, 'propositional_counterexample', side_effect=RuntimeError('broken')) as check:
            result = kurt.check_text('load propositional\nprop A, B, C\nuse A ⇒ B\nuse A ∨ C\nB\n')
            self.assertFalse(result.ok)
            self.assertEqual(check.call_count, 1)
            self.assertEqual(result.error_kind, 'ProofError')
            self.assertIn('`line 3`: missing `A`', result.error)
            self.assertNotIn('counterexample', result.failure)


if __name__ == '__main__':
    unittest.main()
