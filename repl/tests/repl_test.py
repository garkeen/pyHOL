"""Tests for the pyHOL REPL.

The REPL is exercised as a batch session (same code path as interactive
use), asserting: a complete proof reaches VALID, a failing step leaves the
state untouched and reports the real exception, and undo rebuilds.
"""

import io
import contextlib
import unittest

from core import basic
from core import context
from repl.repl import Repl


class ReplTest(unittest.TestCase):
    def setUp(self):
        basic.load_metadata()

    def run_session(self, lines):
        rp = Repl()
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            for line in lines:
                rp.run_line(line)
        return rp, out.getvalue()

    def testSimpleProofReachesValid(self):
        # add_Suc_right, the same proof stored in library/nat.pyhol.
        rp, out = self.run_session([
            'theory nat',
            'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← induct x nat_induct goal=0',
            '← rewrite nat_plus_def_1 sym=false goal=1',
            '← intro m goal=2',
            '← rewrite nat_plus_def_2 sym=false goal=5',
            '← rewrite source=prev goal=6 facts=[4]',
            'check',
        ])
        self.assertIn('VALID', out)
        self.assertEqual(rp.sps.num_gaps, 0)
        # export round-trips back into a proof block.
        rp, out = self.run_session([
            'theory nat', 'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← induct x nat_induct goal=0',
            '← rewrite nat_plus_def_1 sym=false goal=1',
            '← intro m goal=2',
            '← rewrite nat_plus_def_2 sym=false goal=5',
            '← rewrite source=prev goal=6 facts=[4]',
            'export',
        ])
        self.assertIn('proof', out)
        self.assertIn('qed', out)

    def testFailingStepKeepsState(self):
        rp, out = self.run_session([
            'theory nat', 'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← induct x nat_induct goal=0',
            # nat_plus_def_2 cannot rewrite goal 1 (0 + Suc y = ...).
            '← rewrite nat_plus_def_2 sym=false goal=1',
        ])
        self.assertIn('STEP FAILED', out)
        self.assertIn('unable to apply theorem', out)
        # The failed step left no trace: only the induct step is recorded.
        self.assertEqual(len(rp.history), 1)

    def testUndoRebuilds(self):
        rp, out = self.run_session([
            'theory nat', 'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← induct x nat_induct goal=0',
            'undo',
        ])
        self.assertEqual(len(rp.history), 0)
        # Back to the single original goal.
        self.assertEqual([sid for sid, _ in rp.sps.get_open_goals()], [0])

    def testUnknownGoalReportsLiveIds(self):
        rp, out = self.run_session([
            'theory nat', 'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← rewrite nat_plus_def_1 sym=false goal=99',
        ])
        self.assertIn('goal sid 99 not found', out)
        self.assertIn('live sids', out)

    def testVarTypeWithSpace(self):
        # Type strings contain spaces (`'a => bool`); var must not split them.
        rp, out = self.run_session(['theory logic', "var P 'a => bool"])
        self.assertIn("variable P :: 'a => bool", out)
        self.assertEqual(rp.vars['P'], "'a => bool")

    def testVarStepNotSwallowedByCommand(self):
        # `var a 'a goal=N` is the `var` *method* step, not the REPL
        # `var` command; it must reach the proof state.
        rp, out = self.run_session([
            'theory logic', "var P 'a => bool",
            "goal (∃x. P x) ⟷ (∃x1. P x1)",
            '← rule iffI goal=0',
            "var a 'a goal=1",
        ])
        self.assertIn('_VAR a', out)
        self.assertNotIn('usage: var NAME TYPE', out)

    def testMethodsCommandListsUsableMethods(self):
        # `methods` reflects the checked registry, so a listed name is a
        # name a step line may use.
        rp, out = self.run_session(['theory nat', 'methods rewrite'])
        self.assertIn('rewrite', out)
        self.assertIn('params: theorem, sym', out)
        # Unavailable filters out entirely.
        rp, out = self.run_session(['theory nat', 'methods zzz'])
        self.assertIn('0 of', out)

    def testTheoremsAndThmCommands(self):
        # Theorems in scope come from the loaded theory closure, not a guess.
        rp, out = self.run_session(['theory nat', 'theorems less_eq_exist'])
        self.assertIn('less_eq_exist', out)
        self.assertIn('1 of', out)
        # `thm` shows the statement and the rule/forward named arguments.
        rp, out = self.run_session(['theory nat', 'thm less_exist'])
        self.assertIn('?m < ?n', out)
        self.assertIn('param_m', out)
        # A missing name is diagnosed, not fatal.
        rp, out = self.run_session(['theory nat', 'thm no_such_thm_xyz'])
        self.assertIn('no such theorem', out)

    def testResetClearsVarsAndGoal(self):
        # Stale `var` declarations otherwise collide with witness names
        # in a later goal (`elim: duplicate name p`).
        rp, out = self.run_session([
            'theory nat', 'var x nat',
            'goal x = x',
            'reset',
        ])
        self.assertIn('session reset', out)
        self.assertEqual(rp.vars, {})
        self.assertIsNone(rp.sps)

    def testResidentRequestReusesLoadedTheory(self):
        # The resident server executes requests through handle_request;
        # two requests share one Repl, so the theory loads once.
        rp = Repl()
        r1 = rp.handle_request({'cmds': ['theory nat']})
        self.assertIn('theory nat loaded', r1['out'])
        r2 = rp.handle_request({'cmds': [
            'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← induct x nat_induct goal=0',
            '← rewrite nat_plus_def_1 sym=false goal=1',
            '← intro m goal=2',
            '← rewrite nat_plus_def_2 sym=false goal=5',
            '← rewrite source=prev goal=6 facts=[4]',
        ]})
        self.assertEqual(r2['gaps'], 0)
        self.assertFalse(r2['failed'])
        # A failed step is reported in the reply and sets the flag.
        r3 = rp.handle_request({'cmds': ['← rewrite nat_plus_def_1 goal=0']})
        self.assertTrue(r3['failed'])
        self.assertIn('STEP FAILED', r3['out'])


class SemanticRefTest(unittest.TestCase):
    """`goal=@` / `facts=[@]` / quoted references / `let` aliases.

    These replace hand-written stable IDs, which go wrong as soon as a step
    opens or closes several goals (`#[N]` is assigned per proposition, so
    the numbering is not the line number).
    """

    def setUp(self):
        basic.load_metadata()

    def run_session(self, lines):
        rp = Repl()
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            for line in lines:
                rp.run_line(line)
        return rp, out.getvalue()

    def testGoalAutoRefFollowsTheOpenGoal(self):
        # `@` = the goal the previous step opened; when a step closes its
        # own goal (a rewrite that finishes it), it continues on the
        # newest open goal and says so.
        rp, out = self.run_session([
            'theory nat', 'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← induct x nat_induct goal=0',
            '← rewrite nat_plus_def_1 sym=false goal=1',
            '← intro m goal=@',
            '← rewrite nat_plus_def_2 sym=false goal=@',
            'let ih "m + Suc y = Suc (m + y)"',
            '← rewrite source=prev goal=@ facts=[ih]',
            'check',
        ])
        self.assertIn('continuing on the newest open goal', out)
        self.assertIn('VALID', out)
        self.assertEqual(rp.sps.num_gaps, 0)

    def testQuotedFactRefIsBranchChecked(self):
        # The induction-step goal is the *parent* of the goal being proved;
        # it is still a tracked item, but the engine's own dependency rule
        # rejects it (`ItemID.can_depend_on`).  A quoted reference is
        # reported up front instead of failing later with
        # `apply_method: illegal dependence`.
        from repl.repl import RefError
        rp, out = self.run_session([
            'theory nat', 'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← induct x nat_induct goal=0',
            '← rewrite nat_plus_def_1 sym=false goal=1',
            '← intro m goal=@',
            '← rewrite nat_plus_def_2 sym=false goal=@',
        ])
        props = {sid: prop for sid, prop, _ in rp._items()}
        # #2 is the induction-step goal (parent of #6); #3/#4 are facts
        # created inside the current subproof.
        self.assertFalse(rp._in_branch_of(2, 6))
        self.assertTrue(rp._in_branch_of(3, 6))
        with self.assertRaises(RefError) as cm:
            rp.resolve_fact_ref('"%s"' % props[2], 6)
        self.assertIn('cannot depend on', str(cm.exception))
        # Through a step line the same reference fails loudly and leaves the
        # proof state untouched.
        rp.run_line('← rewrite source=prev goal=6 facts=["%s"]' % props[2])
        self.assertTrue(rp.failed)
        self.assertEqual(rp.sps.num_gaps, 1)

    def testFactAutoRefNeedsAFactFromThatStep(self):
        # `facts=[@]` is "what the previous step derived"; a step that only
        # opened a goal has nothing to offer, and saying so beats silently
        # reaching back to an older item.
        rp, out = self.run_session([
            'theory nat', 'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← induct x nat_induct goal=0',
            '← rewrite nat_plus_def_1 sym=false goal=1',
            '← intro m goal=@',
            '← rewrite nat_plus_def_2 sym=false goal=@',
            '← rewrite source=prev goal=@ facts=[@]',
        ])
        self.assertTrue(rp.failed)
        self.assertIn('created no fact', out)

    def testUnknownAliasIsDiagnosed(self):
        rp, out = self.run_session([
            'theory nat', 'var x nat',
            'goal x = x',
            '← rewrite source=prev goal=0 facts=[nope]',
        ])
        self.assertTrue(rp.failed)
        self.assertIn('unknown alias', out)
        self.assertEqual(rp.sps.num_gaps, 1)

    def testItemPrintsPasteableBlock(self):
        # `item` is the write-out step: header + raw statement (annotations
        # kept) + the exported proof.
        rp, out = self.run_session([
            'theory nat', 'var x nat', 'var y nat',
            'goal x + Suc y = Suc (x + y)',
            '← induct x nat_induct goal=0',
            '← rewrite nat_plus_def_1 sym=false goal=1',
            '← intro m goal=@',
            '← rewrite nat_plus_def_2 sym=false goal=@',
            'let ih "m + Suc y = Suc (m + y)"',
            '← rewrite source=prev goal=@ facts=[ih]',
            'item demo',
        ])
        self.assertIn('theorem demo', out)
        self.assertIn('fixes x :: nat, y :: nat', out)
        self.assertIn('prop x + Suc y = Suc (x + y)', out)
        self.assertIn('\nproof\n', out)
        self.assertIn('\nqed', out)

    def testItemKeepsClassAnnotationInTheStatement(self):
        # The item layer re-injects the class premise, so the file must keep
        # the annotation while the proof state works on the desugared prop.
        rp, out = self.run_session([
            'theory order', "var x 'a::linorder",
            'goal x <= x',
            '← intro goal=0',
            '← rule linorder_refl goal="x <= x" facts=[1]',
            'item linorder_le_refl_demo',
        ])
        self.assertIn("fixes x :: 'a::linorder", out)
        self.assertIn('prop x <= x', out)
        self.assertNotIn('prop linorder', out)
        self.assertEqual(rp.sps.num_gaps, 0)


class ServerBindTest(unittest.TestCase):
    def testBindServerFailsWhenPortIsTaken(self):
        # A second server on the same port must fail loudly: on Windows
        # SO_REUSEADDR would let it shadow the live one, so clients would
        # keep talking to stale code after a "restart".
        import socket
        from repl.repl import bind_server
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            sock.bind(('127.0.0.1', 0))
            sock.listen(1)
            port = sock.getsockname()[1]
            with self.assertRaises(OSError):
                bind_server(port)
        finally:
            sock.close()


if __name__ == '__main__':
    unittest.main()
