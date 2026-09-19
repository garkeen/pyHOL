# Tests for the product size family (library/prod_size.pyhol).

"""`prod_size` is the size family `datgen` would have generated with the
datatype, stated in a theory of its own: `prod`'s declaration imports no
arithmetic, so the size's equations (`1 + f a + g b`) can only be written
where `+` is in scope.  What needs it is a recursion on a *tupled*
argument -- a mutual definition's encoded argument is a product -- where
the measure search reads the datatype's size off the theory.

Active: the theory replays VALID, the family is there, and the measure
search finds it (which is what the size is for).
"""

import unittest

from kernel import theory
from kernel.type import TConst
from core import basic
from core import fungen
from core.verify import validate_theory, COMPUTATION_ORACLES

NatType = TConst('nat')

API = ['prod_size_def', 'prod_size_def_1', 'prod_size_exhaustive',
       'prod_size_cases', 'prod_size_elims', 'prod_size_induct']


class ProdSizeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        import method.stable_state  # noqa: F401  wires the replay pipeline
        basic.load_metadata()

    def testTheoryValidates(self):
        for fn in basic.get_import_order(['prod_size']):
            basic.load_theory_cache(fn)
        statuses, errors = validate_theory('prod_size', force=True,
                                           trust=COMPUTATION_ORACLES)
        self.assertEqual(set(statuses.values()), {'VALID'}, errors)

    def testFamilyIsThere(self):
        basic.load_theory('prod_size')
        for name in API:
            self.assertIsNotNone(theory.get_theorem(name), name)

    def testTheMeasureSearchFindsIt(self):
        """A product argument is measured by `prod_size` with `id` at both
        parameters -- one measure per type variable of the datatype."""
        basic.load_theory('prod_size')
        fam = fungen._size_family(TConst('prod', NatType, NatType), set())
        self.assertIsNotNone(fam)
        sz, ptypes, (arity, table) = fam
        self.assertEqual(sz, 'prod_size')
        self.assertEqual(ptypes, [NatType, NatType])
        self.assertEqual(arity, 2)
        self.assertIn('Pair', table)
        self.assertEqual(table['Pair'][0], 'prod_size_def_1')


if __name__ == '__main__':
    unittest.main()
