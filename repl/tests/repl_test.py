"""Tests for the holpy REPL.

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


if __name__ == '__main__':
    unittest.main()
