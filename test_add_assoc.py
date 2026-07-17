import json
import sys
sys.path.insert(0, '.')

from logic import basic
from server import method
from kernel import theory

basic.load_theory('nat')
cache = basic.load_theory_cache('nat')

# Find add_assoc
for item in cache['content']:
    if hasattr(item, 'name') and item.name == 'add_assoc':
        print('=== add_assoc ===')
        print('vars:', item.vars)
        print('prop:', item.prop)
        print()
        print('steps:')
        for i, s in enumerate(item.steps):
            print(f'  step {i}: {s}')
        print()
        print('proof lines:')
        for p in item.proof:
            print(f"  {p['id']}: rule={p['rule']}, th={p['th']}")
        print()
        print('num_gaps:', item.num_gaps)
        break
