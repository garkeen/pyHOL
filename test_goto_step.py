import json
import sys
import copy
sys.path.insert(0, '.')

from logic import basic, context
from server import server, method
from kernel import theory
from syntax import settings

basic.load_theory('nat')

# Get add_assoc data
cache = basic.load_theory_cache('nat')
for item in cache['content']:
    if hasattr(item, 'name') and item.name == 'add_assoc':
        vars_dict = {k: str(v) for k, v in item.vars.items()}
        prop = str(item.prop)
        steps = item.steps
        break

# Simulate what the server does
theory_name = 'nat'
thm_name = 'add_assoc'

# Simulate create_cache
context.set_context(theory_name, limit=('thm', thm_name), vars=item.vars)
state = server.parse_init_state(prop)

history = []
states = [copy.copy(state)]
for step in steps:
    history.extend(state.parse_steps([step]))
    states.append(copy.copy(state))

print(f"Total states: {len(states)}")
print(f"Total history: {len(history)}")
print()

# Show proof at each state
for i, s in enumerate(states):
    with settings.global_setting(unicode=True):
        proof_data = s.json_data()
    
    print(f"=== State {i} (after {i} steps) ===")
    print(f"  proof lines: {len(proof_data['proof'])}")
    print(f"  num_gaps: {proof_data['num_gaps']}")
    for p in proof_data['proof']:
        print(f"    {p['id']}: {p['rule']}")
    print()
