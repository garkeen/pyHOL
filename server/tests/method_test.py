"""Unit test for methods."""

from typing import List, Optional
import unittest

from kernel.term import Var, Term, Implies
from kernel.thm import Thm
from kernel import theory
from framework import context
from server import methods as method
from framework.method import global_methods, get_method
from server import server
from syntax import parser


def test_method(self: unittest.TestCase, thy_name: str, *, vars=None,
                assms: Optional[List[str]] = None, concl: str,
                method_name: str, prevs=None, args=None,
                gaps=None, lines=None, query=None, failed=None):
    """Test run a method.

    gaps -- expected gaps remaining.
    query -- expected query for variables.
    failed -- if None, expected Exception.

    """
    # Build context
    context.set_context(thy_name, vars=vars)

    # Build starting state
    if assms is not None:
        assert isinstance(assms, list), "test_method: assms need to be a list"
        assms = [parser.parse_term(t) for t in assms]
    else:
        assms = []
    concl = parser.parse_term(concl)
    state = server.parse_init_state(Implies(*(assms + [concl])))

    # Obtain and run method
    if args is None:
        args = dict()
    args['method_name'] = method_name
    args['goal_id'] = len(assms)
    args['fact_ids'] = prevs

    if failed is not None:
        self.assertRaises(failed, method.apply_method, state, args)
        return

    if query is not None:
        self.assertRaises(theory.ParameterQueryException, method.apply_method, state, args)
        return

    method.apply_method(state, args)
    self.assertEqual(state.check_proof(), Thm(Implies(*(assms + [concl]))))
    
    # Compare list of gaps
    if gaps is None:
        gaps = [concl]  # gaps unchanged
    elif gaps == False:
        gaps = []  # assert no gaps
    else:
        assert isinstance(gaps, list), "test_method: gaps need to be a list"
        gaps = [parser.parse_term(gap) for gap in gaps]
    self.assertEqual([gap.prop for gap in state.rpt.gaps], gaps)

    # Compare list of lines
    if lines:
        for id, t in lines.items():
            t = parser.parse_term(t)
            self.assertEqual(state.get_proof_item(id).th.prop, t)


# Helper function, not a pytest test
test_method.__test__ = False


class MethodTest(unittest.TestCase):
    def run_search_thm(self, thy_name: str, *, vars=None, assms: Optional[List[str]] = None,
                       concl: str, method_name: str, prevs=None, res, mode=None):
        # Build context
        context.set_context(thy_name, vars=vars)

        # Build starting state
        assms = [parser.parse_term(t) for t in assms] if assms is not None else []
        concl = parser.parse_term(concl)
        state = server.parse_init_state(Implies(*(assms + [concl])))

        # Obtain method and run its search function. Unified dispatchers
        # (rewrite/forward/inst) merge several modes, so filter their
        # results by the mode markers to get a single-mode view.
        method = get_method(method_name)
        search_res = state.apply_search(len(assms), method, prevs=prevs)
        MODE_FILTER = {
            'goal_thm': lambda r: 'target' not in r and 'source' not in r,
            'goal_prev': lambda r: 'target' not in r and r.get('source') == 'prev',
            'fact_thm': lambda r: r.get('target') == 'fact' and 'source' not in r,
            'fact_prev': lambda r: r.get('target') == 'fact' and r.get('source') == 'prev',
            'fwd_thm': lambda r: 'source' not in r,
            'fwd_fact': lambda r: r.get('source') == 'fact',
            'inst_goal': lambda r: r.get('target') == 'goal',
            'inst_fact': lambda r: r.get('target') == 'fact',
        }
        if mode in MODE_FILTER:
            search_res = [r for r in search_res if MODE_FILTER[mode](r)]
        self.assertEqual([res['theorem'] for res in search_res], res)

    def testCases(self):
        test_method(self,
            'logic_base',
            vars={'B': 'bool', 'C': 'bool'},
            concl='B | C',
            method_name='cases',
            args={'case': 'B'},
            gaps=['B --> B | C', '~B --> B | C']
        )

    def testCasesFail(self):
        test_method(self,
            'logic_base',
            vars={'B': 'bool', 'C': 'bool'},
            concl='B | C',
            method_name='cases',
            args={'case': '(A::bool)'},
            failed=AssertionError
        )

    def testGoal(self):
        test_method(self,
            'logic_base',
            vars={'B': 'bool', 'C': 'bool'},
            concl='B & C',
            method_name='cut',
            args={'goal': 'B'},
            gaps=['B', 'B & C']
        )

    def testGoalFail(self):
        test_method(self,
            'logic_base',
            vars={'B': 'bool', 'C': 'bool'},
            concl='B & C',
            method_name='cut',
            args={'goal': '(A::bool)'},
            failed=AssertionError
        )

    def testApplyBackwardStepThms(self):
        self.run_search_thm(
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='B & A',
            method_name='rule',
            res=['conjI']
        )

    def testApplyBackwardStepThms2(self):
        self.run_search_thm(
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A | B'],
            concl='B | A',
            method_name='rule',
            prevs=[0],
            res=['disjE', 'resolution_right']
        )

    def testApplyBackwardStepThms3(self):
        """Example of two results."""
        self.run_search_thm(
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A | B'],
            concl='B | A',
            method_name='rule',
            res=['disjI1', 'disjI2']
        )

    def testApplyBackwardStepThms4(self):
        """Example with no variables."""
        self.run_search_thm(
            'logic_base',
            concl='true',
            method_name='rule',
            res=['trueI']
        )

    def testApplyBackwardStep(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='B & A',
            method_name='rule',
            args={'theorem': 'conjI'},
            gaps=['B', 'A']
        )

    def testApplyBackwardStep2(self):
        """Case where one or more assumption also needs to be matched."""
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A | B'],
            concl='B | A',
            method_name='rule',
            args={'theorem': 'disjE'},
            prevs=[0],
            gaps=['A --> B | A', 'B --> B | A']
        )

    def testApplyBackwardStep3(self):
        """Test when additional instantiation is not provided."""
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='A',
            method_name='rule',
            args={'theorem': 'conjD1'},
            query=['B']
        )

    def testApplyBackwardStep4(self):
        """Test when additional instantiation is not provided."""
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='A',
            method_name='rule',
            args={'theorem': 'conjD1', 'param_B': 'B'},
            gaps=False
        )

    def testApplyBackwardStep5(self):
        """Test case with type variable only."""
        test_method(self,
            'set',
            concl='finite (empty_set::nat set)',
            method_name='rule',
            args={'theorem': 'finite_empty'},
            gaps=False
        )

    def testApplyForwardStepThms(self):
        self.run_search_thm(
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='B & A',
            method_name='forward',
            prevs=[0],
            res=['conjD1', 'conjD2', 'resolution_right', 'weakening'],
            mode='fwd_thm'
        )

    def testApplyForwardStep1(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A & B'],
            concl='B & A',
            method_name='forward',
            args={'theorem': 'conjD1'},
            prevs=[0],
            lines={'1': 'A'}
        )

    def testApplyForwardStep2(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A'],
            concl='A | B',
            method_name='forward',
            args={'theorem': 'disjI1'},
            prevs=[0],
            query=['B']
        )

    def testApplyForwardStep3(self):
        test_method(self,
            'logic_base',
            vars={'A': 'bool', 'B': 'bool'},
            assms=['A'],
            concl='A | B',
            method_name='forward',
            args={'theorem': 'disjI1', 'param_B': 'B'},
            prevs=[0],
            gaps=False
        )

    def testApplyForwardStep4(self):
        test_method(self,
            'set',
            vars={'A': 'nat set', 'B': 'nat set'},
            assms=['A Sub B'],
            concl='false',
            method_name='forward',
            args={'theorem': 'subset_trans', 'param_C': ''},
            prevs=[0],
            lines={'1': '!C. B Sub C --> A Sub C'}
        )

    def testApplyForwardStep5(self):
        test_method(self,
            'set',
            vars={'A': 'nat set', 'B': 'nat set', 'C': 'nat set'},
            assms=['A Sub B'],
            concl='B Sub C',
            method_name='forward',
            args={'theorem': 'subset_trans', 'param_C': 'C'},
            prevs=[0],
            lines={'1': 'B Sub C --> A Sub C'}
        )

    def testApplyForwardStep6(self):
        test_method(self,
            'set',
            vars={'A': 'nat set', 'B': 'nat set', 'C': 'nat set'},
            concl='false',
            method_name='forward',
            args={'theorem': 'subset_trans', 'param_A': 'A', 'param_B': 'B', 'param_C': 'C'},
            lines={'0': 'A Sub B --> B Sub C --> A Sub C'}
        )

    def testApplyResolveStepThms(self):
        """set has no hint_resolve lemmas yet, so nothing applies to x Mem empty_set."""
        self.run_search_thm(
            'set',
            vars={'x': "'a"},
            assms=['x Mem empty_set'],
            concl=['false'],
            method_name='resolve',
            prevs=[0],
            res=[]
        )

    def testApplyResolveStepThms2(self):
        self.run_search_thm(
            'logic_base',
            assms=['false'],
            concl=['false'],
            method_name='resolve',
            prevs=[0],
            res=['not_false_res']
        )

    def testIntroduction(self):
        test_method(self,
            'logic_base',
            vars={'A': "'a => bool", 'B': "'a => bool"},
            concl='!x. A x --> B x',
            method_name='intro',
            args={'names': 'x'},
            gaps=['B x']
        )

    def testApplyInduction(self):
        test_method(self,
            'nat',
            vars={'n': 'nat'},
            concl='n + 0 = n',
            method_name='induct',
            args={'theorem': 'nat_induct', 'var': 'n'},
            gaps=['(0::nat) + 0 = 0', '!n. n + 0 = n --> Suc n + 0 = Suc n']
        )

    def testRewriteGoalThms(self):
        self.run_search_thm(
            'nat',
            vars={'n': 'nat'},
            concl='0 + n = 0',
            method_name='rewrite',
            res=['eq_add_lcancel_0', 'nat_plus_def_1'],
            mode='goal_thm'
        )

    def testRewriteGoalThms2(self):
        self.run_search_thm(
            'set',
            vars={'f': "nat => nat", 'S': "nat set", 'T': "nat set"},
            concl='image f (image f S) = T',
            method_name='rewrite',
            res=['image_combine', 'member_ext', 'set_equal_iff'],
            mode='goal_thm'
        )

    def testRewriteGoal(self):
        test_method(self,
            'logic_base',
            vars={'P': 'bool', 'a': "'a", 'b': "'a"},
            assms=['P'],
            concl='(if P then a else b) = b',
            method_name='rewrite',
            args={'theorem': 'if_P'},
            prevs=[0],
            gaps=['a = b']
        )

    def testRewriteGoal2(self):
        test_method(self,
            'logic_base',
            vars={'P': 'bool', 'a': "'a", 'b': "'a"},
            assms=['P'],
            concl='(if P then a else b) = a',
            method_name='rewrite',
            args={'theorem': 'if_P'},
            prevs=[0],
            gaps=False
        )

    def testRewriteGoal3(self):
        test_method(self,
            'set',
            vars={'g': "'a => 'b", 'f': "'b => 'c", 's': "'a set", 't': "'c set"},
            concl='image f (image g s) = t',
            method_name='rewrite',
            args={'theorem': 'image_combine', 'sym': 'false'},
            gaps=["image (g O f) s = t"]
        )

    def testRewriteGoal4(self):
        test_method(self,
            'set',
            vars={'f': "'a => 'b", 's': "'a set", 't': "'a set"},
            concl='(∃x1. x1 ∈ s) ⟷ x ∈ image f s',
            method_name='rewrite',
            args={'theorem': 'in_image'},
            gaps=["(∃x1. x1 ∈ s) ⟷ (∃x1. x1 ∈ s & x = f x1)"]
        )

    def testRewriteGoalWithPrev(self):
        test_method(self,
            'nat',
            vars={'f': 'nat => nat', 'g': 'nat => nat', 'a': 'nat'},
            assms=['!n. f n = g n'],
            concl='?x. f x = a',
            method_name='rewrite',
            prevs=[0],
            gaps=['?x. g x = a']
        )

    def testRewriteGoalWithPrev2(self):
        test_method(self,
            'nat',
            vars={'f': 'nat => nat => nat', 'g': 'nat => nat => nat'},
            assms=['!m. !n. f m n = g m n'],
            concl='?x. f x x = a',
            method_name='rewrite',
            prevs=[0],
            gaps=['?x. g x x = a']
        )

    def testRewriteFactThms(self):
        self.run_search_thm(
            'nat',
            vars={'n': 'nat'},
            assms=['0 + n = 0'],
            concl='false',
            method_name='rewrite',
            prevs=[0],
            res=['eq_add_lcancel_0', 'nat_plus_def_1'],
            mode='fact_thm'
        )

    def testRewriteFactThms2(self):
        self.run_search_thm(
            'set',
            vars={'f': "nat => nat", 'S': "nat set", 'T': "nat set"},
            assms=['image f (image f S) = T'],
            concl='false',
            method_name='rewrite',
            prevs=[0],
            res=['image_combine', 'member_ext', 'set_equal_iff'],
            mode='fact_thm'
        )

    def testRewriteFactThms3(self):
        self.run_search_thm(
            'set',
            vars={'P': 'bool', 'a': "'a", 'b': "'a", 'c': "'a"},
            assms=['(if P then a else b) = c', 'P'],
            concl='false',
            method_name='rewrite',
            prevs=[0, 1],
            res=['if_P'],
            mode='fact_thm'
        )

    def testRewriteFact(self):
        test_method(self,
            'set',
            vars={'g': "'a => 'b", 'f': "'b => 'c", 's': "'a set", 't': "'c set"},
            assms=['image f (image g s) = t'],
            concl='false',
            method_name='rewrite',
            prevs=[0],
            args={'theorem': 'image_combine', 'sym': 'false', 'target': 'fact'},
            lines={'1': "image (g O f) s = t"}
        )

    def testRewriteFact2(self):
        test_method(self,
            'logic_base',
            vars={'P': 'bool', 'a': "'a", 'b': "'a", 'c': "'a"},
            assms=['(if P then a else b) = c', 'P'],
            concl='false',
            method_name='rewrite',
            args={'theorem': 'if_P', 'target': 'fact'},
            prevs=[0, 1],
            lines={'2': 'a = c'}
        )

    def testRewriteFactWithPrev(self):
        test_method(self,
            'nat',
            vars={'f': 'nat => nat', 'g': 'nat => nat', 'a': 'nat'},
            assms=['!n. f n = g n', '?x. f x = a'],
            concl='false',
            method_name='rewrite',
            prevs=[0, 1],
            args={'target': 'fact', 'source': 'prev'},
            lines={'2': '?x. g x = a'}
        )

    def testForallElim(self):
        test_method(self,
            'nat',
            vars={'n': 'nat', 'P': 'nat => bool', 'Q': 'nat => bool'},
            assms=['!x. P x --> Q x'],
            concl='Q n',
            method_name='inst',
            args={'s': 'n'},
            prevs=[0],
            lines={'1': 'P n --> Q n'}
        )

    def testForallElim2(self):
        test_method(self,
            'nat',
            vars={'n': 'nat', 'P': 'nat => bool', 'Q': 'nat => bool'},
            assms=['!P. P n'],
            concl='Q n',
            method_name='inst',
            args={'s': '%n::nat. n > 2'},
            prevs=[0],
            lines={'1': 'n > 2'}
        )

    def testForallElimFail(self):
        test_method(self,
            'nat',
            vars={'n': 'nat', 'P': 'nat => bool', 'Q': 'nat => bool'},
            assms=['!x. P x --> Q x'],
            concl='Q n',
            method_name='inst',
            args={'s': '(m::nat)'},
            prevs=[0],
            failed=AssertionError
        )

    def testInstExistsGoal(self):
        test_method(self,
            'nat',
            vars={'n': 'nat', 'P': 'nat => bool', 'Q': 'nat => bool'},
            assms=['P n'],
            concl='?x. P x --> Q x',
            method_name='inst',
            args={'s': 'n'},
            gaps=['P n --> Q n']
        )

    def testInstExistsGoalFail(self):
        test_method(self,
            'nat',
            vars={'n': 'nat', 'P': 'nat => bool', 'Q': 'nat => bool'},
            assms=['P n'],
            concl='?x. P x --> Q x',
            method_name='inst',
            args={'s': '(m::nat)'},
            failed=AssertionError
        )

    def testInstExistsFact(self):
        test_method(self,
            'nat',
            assms=['?n::nat. n + 1 = 2'],
            concl='false',
            method_name='elim',
            args={'names': 'n'},
            prevs=[0],
            lines={'1': '_VAR (n::nat)', '2': '(n::nat) + 1 = 2'}
        )

    def testInstExistsFactFail(self):
        test_method(self,
            'nat',
            vars={'n': 'nat'},
            assms=['?n::nat. n + 1 = 2'],
            concl='n = 1',
            method_name='elim',
            args={'names': 'n'},
            prevs=[0],
            failed=AssertionError
        )


class AcceptMethodTest(unittest.TestCase):
    """accept semantics: stripped-conclusion match + C6 whole-prop fallback."""

    def _sps(self, prop, vars, steps=()):
        from server.stable_state import StableProofState
        sps = StableProofState.create(prop, vars)
        for s in steps:
            self.assertTrue(sps.apply_method_dict(s), "step failed: %s" % s)
        return sps

    def testAcceptWholeProp(self):
        """accept closes an implication-shaped goal (not yet intro'd) via
        the C6 whole-prop fallback, recording a single macro line."""
        context.set_context('logic')
        sps = self._sps('~ (p | q) --> ~ q', {'p': 'bool', 'q': 'bool'},
                        [{'method_name': 'rewrite', 'theorem': 'disj_comm',
                          'sym': 'false', 'goal': 0}])
        ok = sps.apply_method_dict({'method_name': 'accept',
                                    'theorem': 'not_or_elim1', 'goal': 1})
        self.assertTrue(ok)
        self.assertEqual(sps.num_gaps, 0)
        # One apply_theorem_inst line replaces the goal; no raw primitive lines.
        items = sps.state.prf.items
        self.assertEqual(len(items), 2)
        self.assertEqual(items[0].rule, 'apply_theorem_inst')
        rpt = sps.state.check_proof(no_gaps=True)
        self.assertTrue(rpt is not None)

    def testAcceptStripped(self):
        """accept on an already-intro'd goal discharges premises from hyps."""
        test_method(self,
            'logic',
            vars={'p': 'bool', 'q': 'bool'},
            assms=['~(p | q)'],
            concl='~p',
            method_name='accept',
            args={'theorem': 'not_or_elim1'},
            gaps=False
        )

    def testAcceptFailsNoMatch(self):
        """accept fails when neither stage matches."""
        context.set_context('logic')
        sps = self._sps('~ (p | q) --> p', {'p': 'bool', 'q': 'bool'})
        ok = sps.apply_method_dict({'method_name': 'accept',
                                    'theorem': 'not_or_elim1', 'goal': 0})
        self.assertFalse(ok)
        self.assertEqual(sps.num_gaps, 1)

    def testAcceptSearchSuggests(self):
        """backward search suggests accept via the C1 exact-match channel."""
        context.set_context('logic')
        sps = self._sps('~ (p | q) --> ~ q', {'p': 'bool', 'q': 'bool'},
                        [{'method_name': 'rewrite', 'theorem': 'disj_comm',
                          'sym': 'false', 'goal': 0}])
        res = sps.search_backward(1, [])
        acc = [r for r in res['results'] if r.get('method_name') == 'accept']
        self.assertTrue(any(r.get('theorem') == 'not_or_elim1' for r in acc))
        self.assertTrue(any(r.get('_goal') == [] for r in acc))
        # rule must NOT be suggested for a theorem that only matches
        # whole-propositionally (no C6 fallback on rule anymore).
        rul = [r for r in res['results'] if r.get('method_name') == 'rule'
               and r.get('theorem') == 'not_or_elim1']
        self.assertEqual(rul, [])

    def testRuleNoWholePropFallback(self):
        """rule has no C6 fallback (MATCH_MP_TAC semantics): it fails on
        an un-intro'd implication goal; accept closes it."""
        context.set_context('logic')
        sps = self._sps('~ (p | q) --> ~ q', {'p': 'bool', 'q': 'bool'},
                        [{'method_name': 'rewrite', 'theorem': 'disj_comm',
                          'sym': 'false', 'goal': 0}])
        ok = sps.apply_method_dict({'method_name': 'rule',
                                    'theorem': 'not_or_elim1', 'goal': 1})
        self.assertFalse(ok)
        self.assertEqual(sps.num_gaps, 1)
        # The goal must be intro'd before rule applies.
        sps2 = self._sps('~ (p | q) --> ~ q', {'p': 'bool', 'q': 'bool'},
                         [{'method_name': 'rewrite', 'theorem': 'disj_comm',
                           'sym': 'false', 'goal': 0}])
        ok2 = sps2.apply_method_dict({'method_name': 'intro', 'goal': 1})
        self.assertTrue(ok2)
        # The inner subgoal (¬q under hyp ¬(q∨p)) carries a new sid.
        inner_sid = sps2.get_open_goals()[0][0]
        ok3 = sps2.apply_method_dict({'method_name': 'accept',
                                      'theorem': 'not_or_elim1', 'goal': inner_sid})
        self.assertTrue(ok3)
        self.assertEqual(sps2.num_gaps, 0)


    def testAcceptPyholRoundTrip(self):
        """accept steps survive .pyhol export/parse (positional theorem)."""
        from syntax import pyhol
        step = {'method_name': 'accept', 'theorem': 'not_or_elim1',
                'goal': 1, 'new_ids': [], 'new_items': []}
        data = {'name': 't', 'imports': ['logic'], 'domains': [],
                'description': '',
                'content': [{'ty': 'thm', 'name': 't',
                             'vars': {'p': 'bool', 'q': 'bool'},
                             'prop': '~ (p | q) --> ~ q', 'attributes': [],
                             'steps': [step]}]}
        text = pyhol.export_pyhol(data)
        parsed = pyhol.parse_pyhol(text)
        self.assertEqual(parsed['content'][0]['steps'][0]['method_name'], 'accept')
        self.assertEqual(parsed['content'][0]['steps'][0]['theorem'], 'not_or_elim1')
        self.assertEqual(parsed['content'][0]['steps'][0]['goal'], 1)


class LineModelTest(unittest.TestCase):
    """Single-line recording and explicit visible closures (line model):
    every goal must be explicitly introduced and closed, and each
    method step records a bounded number of lines (no primitive chains).
    """

    def _sps(self, prop, vars, steps=()):
        from server.stable_state import StableProofState
        sps = StableProofState.create(prop, vars)
        for s in steps:
            self.assertTrue(sps.apply_method_dict(s), "step failed: %s" % s)
        return sps

    def _rules(self, sps):
        return [l['rule'] for l in sps._export_proof_lines()]

    def testIntroNoFakeCloseLine(self):
        """Plain intro hides its intros frame: no spurious auto_close line."""
        context.set_context('logic')
        sps = self._sps('A --> B', {'A': 'bool', 'B': 'bool'},
                        [{'method_name': 'intro', 'goal': 0}])
        self.assertEqual(self._rules(sps), ['subproof', 'assume', 'sorry'])

    def testAutoCloseLineVisible(self):
        """Explicit auto-closure records a VISIBLE auto_close line."""
        context.set_context('logic')
        sps = self._sps('(A & B) --> A', {'A': 'bool', 'B': 'bool'},
                        [{'method_name': 'intro', 'goal': 0}])
        inner = sps.get_open_goals()[0][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'forward', 'theorem': 'conjD1',
             'goal': inner, 'facts': [1]}))
        self.assertIn('auto_close', self._rules(sps))

    def testAcceptStrippedSingleLine(self):
        """accept stage 1 records ONE accept line (no assume noise)."""
        context.set_context('logic')
        sps = self._sps('~ (p | q) --> ~ p', {'p': 'bool', 'q': 'bool'},
                        [{'method_name': 'intro', 'goal': 0}])
        inner = sps.get_open_goals()[0][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'accept', 'theorem': 'not_or_elim1', 'goal': inner}))
        self.assertEqual(self._rules(sps), ['subproof', 'assume', 'accept'])
        self.assertEqual(sps.num_gaps, 0)

    def testSimpSingleLine(self):
        """simp records one simp line + the new-goal sorry (no conv chain)."""
        context.set_context('logic')
        sps = self._sps('(p & q) & r = p & (q & r)',
                        {'p': 'bool', 'q': 'bool', 'r': 'bool'},
                        [{'method_name': 'simp', 'goal': 0}])
        self.assertEqual(self._rules(sps), ['sorry', 'simp'])
        self.assertEqual(sps.num_gaps, 1)

    def testAutoClosesIff(self):
        """auto closes A <--> B from the two implications in one line."""
        context.set_context('logic')
        sps = self._sps('(A --> B) --> (B --> A) --> (A <--> B)',
                        {'A': 'bool', 'B': 'bool'},
                        [{'method_name': 'intro', 'goal': 0}])
        inner = sps.get_open_goals()[0][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'auto', 'goal': inner, 'facts': [1, 2]}))
        self.assertEqual(sps.num_gaps, 0)
        self.assertIn('auto', self._rules(sps))

    def testAutoHonestFailure(self):
        """auto on a bare variable goal fails without closing anything."""
        context.set_context('logic')
        sps = self._sps('C', {'C': 'bool'}, [])
        self.assertFalse(sps.apply_method_dict(
            {'method_name': 'auto', 'goal': 0}))
        self.assertEqual(sps.num_gaps, 1)

    def testNormInt(self):
        """norm closes an int polynomial equality via int_norm."""
        context.set_context('int')
        sps = self._sps('x + 0 = x', {'x': 'int'},
                        [{'method_name': 'norm', 'goal': 0}])
        self.assertEqual(sps.num_gaps, 0)
        self.assertIn('int_norm', self._rules(sps))

    def testUnfoldSingleLine(self):
        context.set_context('logic')
        sps = self._sps('(A & B) = (B & A)', {'A': 'bool', 'B': 'bool'},
                        [{'method_name': 'unfold', 'theorem': 'conj_comm', 'goal': 0}])
        self.assertEqual(self._rules(sps), ['sorry', 'unfold'])

    def testRewriteLocSingleLine(self):
        """loc rewrite records one rewrite_goal_loc line; reflexive result
        closes without a sorry."""
        context.set_context('logic')
        sps = self._sps('(A & B) = (B & A)', {'A': 'bool', 'B': 'bool'},
                        [{'method_name': 'rewrite', 'theorem': 'conj_comm',
                          'loc': '1', 'goal': 0}])
        self.assertEqual(self._rules(sps), ['rewrite_goal_loc'])
        self.assertEqual(sps.num_gaps, 0)

    def testResolveC4ShapesSingleLine(self):
        """resolve with A --> false / A = false shapes closes with one
        resolve_theorem line."""
        from kernel.term import Var, Eq
        from syntax.logicops import false
        from kernel.type import BoolType
        from kernel.thm import Thm
        # Theorems are stored with plain Vars; get_theorem converts
        # them to schematic variables on retrieval.
        A_v = Var('A', BoolType)
        context.set_context('logic_base')
        theory.thy.add_theorem('__test_A_imp_false', Thm(Implies(A_v, false)))
        theory.thy.add_theorem('__test_A_eq_false', Thm(Eq(A_v, false)))
        for thm_name in ('__test_A_imp_false', '__test_A_eq_false'):
            sps = self._sps('A --> B', {'A': 'bool', 'B': 'bool'},
                            [{'method_name': 'intro', 'goal': 0}])
            inner = sps.get_open_goals()[0][0]
            ok = sps.apply_method_dict({'method_name': 'resolve', 'theorem': thm_name,
                                        'goal': inner, 'facts': [1]})
            self.assertTrue(ok, thm_name)
            self.assertEqual(sps.num_gaps, 0)
            self.assertIn('resolve_theorem', self._rules(sps))

    def testResolveNotAShape(self):
        """resolve with the ~A shape records one resolve_theorem line."""
        context.set_context('logic_base')
        sps = self._sps('false --> B', {'B': 'bool'},
                        [{'method_name': 'intro', 'goal': 0}])
        inner = sps.get_open_goals()[0][0]
        ok = sps.apply_method_dict({'method_name': 'resolve',
                                    'theorem': 'not_false_res',
                                    'goal': inner, 'facts': [1]})
        self.assertTrue(ok)
        self.assertEqual(sps.num_gaps, 0)
        self.assertIn('resolve_theorem', self._rules(sps))

    def _meta(self, sps, item_id):
        for l in sps._export_proof_lines():
            if l['id'] == item_id:
                return l
        return None

    def testCutOrigin(self):
        """cut inserts a sorry line marked with origin='cut'."""
        context.set_context('logic')
        sps = self._sps('A', {'A': 'bool'},
                        [{'method_name': 'cut', 'cut_goal': 'A', 'goal': 0}])
        cut_line = self._meta(sps, '0')
        self.assertEqual(cut_line['rule'], 'sorry')
        self.assertEqual(cut_line['origin'], 'cut')

    def testCutOriginInherited(self):
        """A cut goal covered by a rule keeps origin='cut' on the closing
        line, and the exported subgoals do NOT inherit it (no stale meta)."""
        context.set_context('logic')
        sps = self._sps('(A & B) --> A', {'A': 'bool', 'B': 'bool'},
                        [{'method_name': 'intro', 'goal': 0}])
        inner = sps.get_open_goals()[0][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'cut', 'cut_goal': 'A & B', 'goal': inner}))
        cut_goal = [sid for sid, th in sps.get_open_goals()
                    if str(th.prop) == 'A & B'][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'rule', 'theorem': 'conjI', 'goal': cut_goal}))
        lines = {l['id']: l for l in sps._export_proof_lines()}
        closing = [l for l in lines.values() if l['rule'] == 'apply_theorem'][0]
        self.assertEqual(closing['origin'], 'cut')
        for l in lines.values():
            if l['rule'] == 'sorry':
                self.assertIsNone(l['origin'], l['id'])

    def testForwardLineNoGoalPos(self):
        """Forward fact lines are have-lines (goal_pos False)."""
        context.set_context('logic')
        sps = self._sps('(A & B) --> A', {'A': 'bool', 'B': 'bool'},
                        [{'method_name': 'intro', 'goal': 0}])
        inner = sps.get_open_goals()[0][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'forward', 'theorem': 'conjD1',
             'goal': inner, 'facts': [1]}))
        for l in sps._export_proof_lines():
            if l['rule'] == 'apply_theorem_for':
                self.assertFalse(l['goal_pos'])

    def testManualApplyPrev(self):
        """A manual apply_prev closure exports as rule='apply_prev'
        (vs auto_close for automatic ones) and keeps the cut origin."""
        context.set_context('logic')
        sps = self._sps('B --> A --> C', {'A': 'bool', 'B': 'bool', 'C': 'bool'},
                        [{'method_name': 'intro', 'goal': 0}])
        inner = sps.get_open_goals()[0][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'cut', 'cut_goal': 'A', 'goal': inner}))
        p2s = sps._build_pos2sid()
        cut_goal = [sid for sid, th in sps.get_open_goals()
                    if str(th.prop) == 'A' and len(th.hyps) == 2][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'apply_prev', 'goal': cut_goal,
             'facts': [p2s['0.1']]}))
        line = self._meta(sps, '0.2')
        self.assertEqual(line['rule'], 'apply_prev')
        self.assertEqual(line['origin'], 'cut')
        self.assertEqual(line['prevs'], [p2s['0.1']])

    def testCasesLabels(self):
        """cases branches carry case labels (case expression)."""
        context.set_context('logic')
        sps = self._sps('(A | B) --> (B | A)', {'A': 'bool', 'B': 'bool'},
                        [{'method_name': 'intro', 'goal': 0}])
        inner = sps.get_open_goals()[0][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'cases', 'case': 'A', 'goal': inner}))
        lines = {l['id']: l for l in sps._export_proof_lines()}
        self.assertEqual(lines['0.1']['rule'], 'sorry')
        self.assertEqual(lines['0.1']['case'], 'A')
        self.assertEqual(lines['0.2']['case'], '¬A')

    def testInductLabels(self):
        """induct branches carry case labels reconstructed from the
        induction theorem's premises."""
        context.set_context('nat')
        sps = self._sps('n + 0 = n', {'n': 'nat'},
                        [{'method_name': 'induct', 'theorem': 'nat_induct',
                          'var': 'n', 'goal': 0}])
        lines = {l['id']: l for l in sps._export_proof_lines()}
        self.assertEqual(lines['0']['case'], '(0::nat)')
        self.assertEqual(lines['1']['case'], 'Suc n')

    def testElimObtain(self):
        """elim records an explicit obtain line witnessing the exists
        fact with the fresh variable and body."""
        context.set_context('nat')
        sps = self._sps('(∃n::nat. n + 1 = 2) --> false', {},
                        [{'method_name': 'intro', 'goal': 0}])
        inner = sps.get_open_goals()[0][0]
        self.assertTrue(sps.apply_method_dict(
            {'method_name': 'elim', 'names': 'n', 'goal': inner,
             'facts': [1]}))
        obtain = [l for l in sps._export_proof_lines() if l['rule'] == 'obtain']
        self.assertEqual(len(obtain), 1)
        self.assertEqual(obtain[0]['args'], 'n where n + 1 = 2')
        self.assertEqual(len(obtain[0]['prevs']), 1)


if __name__ == "__main__":
    unittest.main()
