"""
Test script for holpy backend APIs.
Tests: loading theories, adding theorems/axioms, saving to .pyhol, persistence.
"""
import json
import os
import sys
import shutil

sys.path.insert(0, '.')

from app.app import app as flask_app
from logic import basic
from syntax import pyhol

# Real library dir
LIBRARY_DIR = basic.user_dir()


def test_find_files(client):
    """Test /api/find-files endpoint."""
    print("\n=== Test: find-files ===")
    resp = client.post('/api/find-files', json={})
    assert resp.status_code == 200, f"Expected 200, got {resp.status_code}"
    data = resp.get_json()
    assert 'theories' in data
    theories = data['theories']
    print(f"  Found {len(theories)} theories: {theories[:5]}...")
    assert len(theories) > 0
    print("  [PASS]")
    return theories


def test_load_json_file(client, filename='logic_base'):
    """Test /api/load-json-file endpoint."""
    print(f"\n=== Test: load-json-file ({filename}) ===")
    resp = client.post('/api/load-json-file', json={
        'filename': filename,
        'line_length': 80
    })
    assert resp.status_code == 200, f"Expected 200, got {resp.status_code}"
    data = resp.get_json()
    assert 'name' in data and 'content' in data
    assert data['name'] == filename
    item_types = {}
    for item in data['content']:
        ty = item.get('ty', '?')
        item_types[ty] = item_types.get(ty, 0) + 1
    print(f"  Loaded {len(data['content'])} items, types: {item_types}")
    print("  [PASS]")
    return data


def test_save_round_trip(client, filename='logic_base'):
    """Test save-file: save loaded content back, reload and verify counts match."""
    print(f"\n=== Test: save round-trip ({filename}) ===")
    resp = client.post('/api/load-json-file', json={'filename': filename, 'line_length': 80})
    data = resp.get_json()
    orig_count = len(data['content'])
    print(f"  Original: {orig_count} items")

    resp = client.post('/api/save-file', json={'filename': filename, 'content': data})
    assert resp.status_code == 200

    pyhol_path = os.path.join(LIBRARY_DIR, f'{filename}.pyhol')
    with open(pyhol_path, 'r', encoding='utf-8') as f:
        disk = pyhol.parse_pyhol(f.read())
    assert len(disk['content']) == orig_count
    print(f"  On disk: {len(disk['content'])} items")

    resp = client.post('/api/load-json-file', json={'filename': filename, 'line_length': 80})
    reloaded = resp.get_json()
    assert len(reloaded['content']) == orig_count
    print(f"  Reloaded: {len(reloaded['content'])} items")
    print("  [PASS]")


def test_add_axiom_and_persist(client, filename='logic_base'):
    """Add a new axiom, save, verify on disk, reload, then clean up."""
    print(f"\n=== Test: add axiom + persist ({filename}) ===")
    resp = client.post('/api/load-json-file', json={'filename': filename, 'line_length': 80})
    data = resp.get_json()
    old_count = len(data['content'])

    new_axiom = {
        'ty': 'thm.ax',
        'name': '__test_persistence_axiom__',
        'vars': {'A': 'bool', 'B': 'bool'},
        'prop': 'A \u27f6 B \u27f6 A',
        'attributes': []
    }
    data['content'].append(new_axiom)
    print(f"  Added axiom, count: {old_count} -> {len(data['content'])}")

    resp = client.post('/api/save-file', json={'filename': filename, 'content': data})
    assert resp.status_code == 200

    # Verify on disk
    pyhol_path = os.path.join(LIBRARY_DIR, f'{filename}.pyhol')
    with open(pyhol_path, 'r', encoding='utf-8') as f:
        disk = pyhol.parse_pyhol(f.read())
    assert len(disk['content']) == old_count + 1
    found = any(it.get('name') == '__test_persistence_axiom__' for it in disk['content'])
    assert found, "Axiom not found on disk!"
    print("  Verified on disk")

    # Reload via API
    resp = client.post('/api/load-json-file', json={'filename': filename, 'line_length': 80})
    reloaded = resp.get_json()
    assert len(reloaded['content']) == old_count + 1
    found2 = any(isinstance(it, dict) and it.get('name') == '__test_persistence_axiom__'
                 for it in reloaded['content'])
    assert found2, "Axiom not found after reload!"
    print("  Verified after reload")

    # Clean up
    data['content'] = [it for it in data['content']
                       if not (isinstance(it, dict) and it.get('name') == '__test_persistence_axiom__')]
    resp = client.post('/api/save-file', json={'filename': filename, 'content': data})
    assert resp.status_code == 200
    print("  Cleaned up test axiom")
    print("  [PASS]")


def test_add_definition_and_persist(client, filename='logic_base'):
    """Add a new constant definition, save, verify, clean up."""
    print(f"\n=== Test: add definition + persist ({filename}) ===")
    resp = client.post('/api/load-json-file', json={'filename': filename, 'line_length': 80})
    data = resp.get_json()
    old_count = len(data['content'])

    new_def = {
        'ty': 'def.ax',
        'name': '__test_const__',
        'type': 'bool \u21d2 bool'
    }
    data['content'].append(new_def)

    resp = client.post('/api/save-file', json={'filename': filename, 'content': data})
    assert resp.status_code == 200

    pyhol_path = os.path.join(LIBRARY_DIR, f'{filename}.pyhol')
    with open(pyhol_path, 'r', encoding='utf-8') as f:
        disk = pyhol.parse_pyhol(f.read())
    assert len(disk['content']) == old_count + 1
    found = any(it.get('name') == '__test_const__' and it.get('ty') == 'def.ax'
                for it in disk['content'])
    assert found, "Definition not found on disk!"
    print("  Verified definition on disk")

    # Clean up
    data['content'] = [it for it in data['content']
                       if not (isinstance(it, dict) and it.get('name') == '__test_const__')]
    resp = client.post('/api/save-file', json={'filename': filename, 'content': data})
    assert resp.status_code == 200
    print("  Cleaned up")
    print("  [PASS]")


def test_create_new_theory_file(client):
    """Create a brand new theory file, save, verify, clean up."""
    print(f"\n=== Test: create new theory file ===")
    new_theory = {
        'name': '__test_new_theory__',
        'imports': [],
        'description': 'Temporary test theory',
        'content': [
            {'ty': 'header', 'name': 'Definitions', 'depth': 0},
            {'ty': 'def.ax', 'name': 'my_const', 'type': 'bool'},
            {'ty': 'thm.ax', 'name': 'my_axiom', 'vars': {'P': 'bool'},
             'prop': 'P \u27f6 P', 'attributes': []}
        ]
    }

    resp = client.post('/api/save-file', json={
        'filename': '__test_new_theory__', 'content': new_theory
    })
    assert resp.status_code == 200

    pyhol_path = os.path.join(LIBRARY_DIR, '__test_new_theory__.pyhol')
    assert os.path.exists(pyhol_path), "File not created!"
    with open(pyhol_path, 'r', encoding='utf-8') as f:
        disk = pyhol.parse_pyhol(f.read())
    assert disk['name'] == '__test_new_theory__'
    assert len(disk['content']) == 3
    assert disk['content'][0]['ty'] == 'header'
    assert disk['content'][1]['ty'] == 'def.ax'
    assert disk['content'][2]['ty'] == 'thm.ax'
    print(f"  Created {pyhol_path} with {len(disk['content'])} items")

    # Clean up
    os.remove(pyhol_path)
    print("  Cleaned up")
    print("  [PASS]")


def test_check_modify(client, filename='logic_base'):
    """Test /api/check-modify with a constant definition."""
    print(f"\n=== Test: check-modify ({filename}) ===")
    item = {'ty': 'def.ax', 'name': '__test_check__', 'type': 'bool \u21d2 bool'}
    resp = client.post('/api/check-modify', json={
        'filename': filename, 'line_length': 80, 'item': item
    })
    assert resp.status_code == 200
    result = resp.get_json()
    assert 'item' in result
    checked = result['item']
    has_error = 'error' in checked
    print(f"  Result: ty={checked.get('ty')}, name={checked.get('name')}, error={has_error}")
    if has_error:
        print(f"  Error detail: {checked['error'].get('err_str', '?')}")
    print("  [PASS]")


def test_check_modify_no_limit(client, filename='logic_base'):
    """Test /api/check-modify WITHOUT limit_ty/limit_name (new item flow)."""
    print(f"\n=== Test: check-modify without limit ({filename}) ===")
    item = {'ty': 'thm.ax', 'name': '__test_no_limit_axiom__', 'vars': {'P': 'bool'},
            'prop': 'P \u27f6 P', 'attributes': []}
    # No limit_ty or limit_name - simulates frontend creating a new item
    resp = client.post('/api/check-modify', json={
        'filename': filename, 'line_length': 80, 'item': item
    })
    assert resp.status_code == 200, f"Expected 200, got {resp.status_code}"
    result = resp.get_json()
    assert 'item' in result
    checked = result['item']
    has_error = 'error' in checked
    print(f"  Result: ty={checked.get('ty')}, name={checked.get('name')}, error={has_error}")
    if has_error:
        print(f"  Error detail: {checked['error'].get('err_str', '?')}")
    print("  [PASS]")


def test_new_theorem_prove_flow(client, filename='logic_base'):
    """Simulate full flow: check-modify (no limit) then init-saved-proof."""
    print(f"\n=== Test: new theorem prove flow ({filename}) ===")
    
    # Step 1: check-modify for a new axiom (no limit)
    item = {'ty': 'thm.ax', 'name': '__test_prove_flow__', 'vars': {'A': 'bool'},
            'prop': 'A \u27f6 A', 'attributes': []}
    resp = client.post('/api/check-modify', json={
        'filename': filename, 'line_length': 80, 'item': item
    })
    assert resp.status_code == 200
    checked = resp.get_json()['item']
    assert 'error' not in checked, f"check-modify failed: {checked.get('error')}"
    print(f"  Step 1: check-modify OK, name={checked['name']}")
    
    # Step 2: init-saved-proof with the new theorem's data
    resp = client.post('/api/init-saved-proof', json={
        'theory_name': filename,
        'thm_name': checked['name'],
        'vars': checked.get('vars', {}),
        'prop': checked['prop'],
        'steps': [],
    })
    assert resp.status_code == 200, f"init-saved-proof failed: {resp.status_code}"
    data = resp.get_json()
    assert 'state' in data or 'error' in data
    if 'state' in data:
        print(f"  Step 2: init-saved-proof OK, num_gaps={data.get('num_gaps')}")
        assert 'proof' in data['state']
        print(f"  Proof lines: {len(data['state']['proof'])}")
    else:
        print(f"  Step 2: error: {data.get('error')}")
    print("  [PASS]")


def test_init_saved_proof(client, filename='logic_base'):
    """Test /api/init-saved-proof with a trivial proposition."""
    print(f"\n=== Test: init-saved-proof ({filename}) ===")
    resp = client.post('/api/init-saved-proof', json={
        'theory_name': filename,
        'thm_name': '',
        'vars': {'A': 'bool'},
        'prop': 'A \u27f6 A',
        'steps': [],
    })
    assert resp.status_code == 200
    data = resp.get_json()
    if 'state' in data:
        print(f"  State loaded, num_gaps={data.get('num_gaps')}")
    else:
        print(f"  Error: {data.get('error', '?')}")
    print("  [PASS]")


def test_find_link(client, filename='logic_base'):
    """Test /api/find-link for a known axiom."""
    print(f"\n=== Test: find-link ({filename}) ===")
    resp = client.post('/api/find-link', json={
        'filename': filename, 'ext_ty': 'thm.ax', 'name': 'conjI'
    })
    assert resp.status_code == 200
    data = resp.get_json()
    print(f"  Result: {data}")
    print("  [PASS]")


def test_remove_file(client):
    """Create a temp file, then remove it via API."""
    print(f"\n=== Test: remove-file ===")
    tmp_name = '__test_remove__'
    tmp_path = os.path.join(LIBRARY_DIR, f'{tmp_name}.pyhol')
    with open(tmp_path, 'w', encoding='utf-8') as f:
        f.write(pyhol.export_pyhol({'name': tmp_name, 'imports': [], 'description': '', 'content': []}))
    assert os.path.exists(tmp_path)

    resp = client.put('/api/remove-file', json={'filename': tmp_name})
    assert resp.status_code == 200
    assert not os.path.exists(tmp_path), "File not removed!"
    print("  File created and removed successfully")
    print("  [PASS]")


def run_all_tests():
    flask_app.config['TESTING'] = True
    client = flask_app.test_client()

    tests = [
        ("find-files",           lambda: test_find_files(client)),
        ("load-json-file",       lambda: test_load_json_file(client)),
        ("save-round-trip",      lambda: test_save_round_trip(client)),
        ("add-axiom-persist",    lambda: test_add_axiom_and_persist(client)),
        ("add-def-persist",      lambda: test_add_definition_and_persist(client)),
        ("create-new-theory",    lambda: test_create_new_theory_file(client)),
        ("check-modify",         lambda: test_check_modify(client)),
        ("check-modify-no-limit", lambda: test_check_modify_no_limit(client)),
        ("new-theorem-prove-flow", lambda: test_new_theorem_prove_flow(client)),
        ("init-saved-proof",     lambda: test_init_saved_proof(client)),
        ("find-link",            lambda: test_find_link(client)),
        ("remove-file",          lambda: test_remove_file(client)),
    ]

    passed = failed = 0
    errors = []
    for name, fn in tests:
        try:
            fn()
            passed += 1
        except Exception as e:
            failed += 1
            errors.append((name, str(e)))
            import traceback
            traceback.print_exc()

    print("\n" + "=" * 60)
    print(f"RESULTS: {passed} passed, {failed} failed / {len(tests)} total")
    if errors:
        print("\nFailed:")
        for n, e in errors:
            print(f"  - {n}: {e}")
    print("=" * 60)
    return failed == 0


if __name__ == '__main__':
    success = run_all_tests()
    sys.exit(0 if success else 1)
