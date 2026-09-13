"""Step-line parsing: bracket lists tolerate a space after a comma.

`facts=[1, 2]` used to break, because the tokenizer splits on whitespace and
the two halves no longer match the `facts=` pattern.  The bracket list is now
extracted from the raw line first (a malformed, non-numeric bracket still
takes the old path, so nothing about the failure diagnostics changed).
"""

import unittest

from syntax import pyhol


class StepLineTest(unittest.TestCase):
    def testFactsListWithSpaces(self):
        step = pyhol._parse_step_line('← rewrite source=prev goal=6 facts=[4, 5]')
        self.assertEqual(step['method_name'], 'rewrite')
        self.assertEqual(step['goal'], 6)
        self.assertEqual(step['facts'], [4, 5])

    def testFactsListWithoutSpaces(self):
        step = pyhol._parse_step_line('→ forward conjD1 goal=4 facts=[3]')
        self.assertEqual(step['facts'], [3])

    def testEmptyFactsList(self):
        step = pyhol._parse_step_line('← intro goal=0 facts=[]')
        self.assertEqual(step['facts'], [])

    def testNewIdsListWithSpaces(self):
        step = pyhol._parse_step_line('← rule iffI goal=0 new_ids=[1, 2]')
        self.assertEqual(step['new_ids'], [1, 2])

    def testNonNumericBracketIsLeftAlone(self):
        step = pyhol._parse_step_line('← rewrite source=prev goal=6 facts=[x, y]')
        self.assertEqual(step['goal'], 6)
        self.assertNotIsInstance(step.get('facts'), list)


if __name__ == '__main__':
    unittest.main()
