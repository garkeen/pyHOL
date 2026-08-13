"""Unit test for methods."""

from typing import List, Optional
import unittest

from kernel.term import Var, Term, Implies
from kernel.thm import Thm
from kernel import theory
from framework import context
from server import methods as method
from server.methods.core import global_methods, get_method
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


if __name__ == "__main__":
    unittest.main()
