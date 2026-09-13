"""Real pytest coverage for the /api/* surface.

Replaces the 2026-09-09 knowledge-archive version of this file, which
had 12 pytest errors (no client fixture) and whose save round-trip
wrote the *real* library/ (once polluting logic_base.pyhol).  The
sandbox fixture below closes both holes:

* ``core.basic`` resolves every path from its module-level ``dirname``,
  so it is repointed at a tmp dir; ``save_user_file`` is additionally
  pinned to that tmp library so no test can write a real file.
* ``_lib_dirs`` keeps the real ``library/`` as a *read-only* fallback so
  theories that import ``logic_base`` still load; the status cache dir
  is repointed too, so validation does not touch the repo's ``.cache/``.

Only the endpoint payload shape and the read/save/validate round trip
are asserted here; the proof-search semantics are covered by the
method/theories test suites.
"""

import json
import os

import pytest

from backend import app as flask_app
from core import basic
from core import verify
from syntax import pyhol

# Capture the real root before any fixture monkeypatches basic.dirname.
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(basic.__file__)))
REAL_LIB = os.path.join(ROOT, 'library')

DEMO_THEORY = """\
theory demo
imports logic_base

header "Demo"

axiom my_ax
  fixes A :: bool
  prop A \u27f6 A

theorem self_imp
  fixes A :: bool
  prop A \u27f6 A
proof
  \u2190 intro goal=0
qed
"""

DEMO_ITEMS = 3  # header, axiom, theorem


@pytest.fixture
def sandbox(tmp_path, monkeypatch):
    """Isolated library/ + .cache/; real library/ stays read-only."""
    lib = tmp_path / 'library'
    lib.mkdir()
    (tmp_path / 'imperative' / 'programs').mkdir(parents=True)
    cache = tmp_path / '.cache'
    cache.mkdir()

    monkeypatch.setattr(basic, 'dirname', str(tmp_path))
    monkeypatch.setattr(
        basic, '_lib_dirs',
        lambda: [str(lib) + os.sep, REAL_LIB + os.sep])
    monkeypatch.setattr(basic, '_status_cache_dir', lambda: str(cache))
    monkeypatch.setattr(
        basic, 'save_user_file',
        lambda filename: os.path.join(str(lib), filename + '.pyhol'))

    basic.theory_cache.clear()
    basic.statuses.clear()
    basic.errors.clear()
    yield tmp_path
    basic.theory_cache.clear()
    basic.statuses.clear()
    basic.errors.clear()


@pytest.fixture
def client():
    return flask_app.test_client()


def post(client, path, payload):
    return client.post(path, data=json.dumps(payload),
                       content_type='application/json')


def put(client, path, payload):
    return client.put(path, data=json.dumps(payload),
                      content_type='application/json')


def write_demo(sandbox):
    path = sandbox / 'library' / 'demo.pyhol'
    path.write_text(DEMO_THEORY, encoding='utf-8')
    return path


def strip_display(content):
    """Mimic the frontend's persist(): keep core fields only."""
    out = []
    for item in content:
        copy = {k: v for k, v in item.items()
                if k not in ('display', 'edit', 'ext', 'error')}
        out.append(copy)
    return out


# ── theory listing / loading ─────────────────────────────────────

def test_find_files_lists_sandbox_theory(client, sandbox):
    write_demo(sandbox)
    res = post(client, '/api/find-files', {})
    assert res.status_code == 200
    # Real library theories are visible read-only, plus the sandbox one.
    assert 'demo' in res.get_json()['theories']
    assert 'logic_base' in res.get_json()['theories']


def test_load_json_file_shape(client, sandbox):
    write_demo(sandbox)
    res = post(client, '/api/load-json-file',
               {'filename': 'demo', 'line_length': 80})
    assert res.status_code == 200
    data = res.get_json()
    assert data['name'] == 'demo'
    assert data['imports'] == ['logic_base']
    tys = [item['ty'] for item in data['content']]
    assert tys == ['header', 'thm.ax', 'thm']
    # export_web() attaches display/edit/ext to every item.
    for item in data['content']:
        assert 'display' in item and 'edit' in item and 'ext' in item


def test_load_json_file_serves_typeabbrev(client, sandbox):
    (sandbox / 'library' / 'abbr.pyhol').write_text(
        "theory abbr\nimports logic_base\n\n"
        "typeabbrev set2 'a = 'a \u21d2 bool\n",
        encoding='utf-8')
    res = post(client, '/api/load-json-file', {'filename': 'abbr'})
    item = res.get_json()['content'][0]
    assert item['ty'] == 'type.abbrev'
    assert item['name'] == 'set2'
    assert item['args'] == ['a']
    # export_json prints ASCII (round-trip input); display is highlighted
    # AST segments (unicode), which the frontend joins via formatDisplay.
    assert item['def'] == "'a => bool"
    assert ''.join(seg['text'] for seg in item['display']['def']) == "'a \u21d2 bool"


# ── save / round trip ────────────────────────────────────────────

def test_save_round_trip(client, sandbox):
    write_demo(sandbox)
    loaded = post(client, '/api/load-json-file', {'filename': 'demo'}).get_json()
    res = post(client, '/api/save-file', {
        'filename': 'demo',
        'content': {
            'name': 'demo',
            'imports': loaded['imports'],
            'domains': loaded.get('domains', []),
            'description': loaded.get('description', ''),
            'content': strip_display(loaded['content']),
        },
    })
    assert res.status_code == 200
    reparsed = pyhol.parse_pyhol(
        (sandbox / 'library' / 'demo.pyhol').read_text(encoding='utf-8'))
    assert len(reparsed['content']) == DEMO_ITEMS
    reloaded = post(client, '/api/load-json-file', {'filename': 'demo'}).get_json()
    assert len(reloaded['content']) == DEMO_ITEMS


def test_create_new_theory_file(client, sandbox):
    content = [
        {'ty': 'header', 'depth': 0, 'name': 'New'},
        {'ty': 'thm.ax', 'name': '__new_ax__', 'vars': {'A': 'bool'},
         'prop': 'A \u27f6 A'},
    ]
    res = post(client, '/api/save-file', {
        'filename': '__test_new__',
        'content': {'name': '__test_new__', 'imports': ['logic_base'],
                    'domains': [], 'description': 'temp', 'content': content},
    })
    assert res.status_code == 200
    path = sandbox / 'library' / '__test_new__.pyhol'
    assert path.exists()
    assert len(pyhol.parse_pyhol(path.read_text(encoding='utf-8'))['content']) == 2
    loaded = post(client, '/api/load-json-file', {'filename': '__test_new__'})
    assert len(loaded.get_json()['content']) == 2


def test_remove_file(client, sandbox):
    path = write_demo(sandbox)
    res = put(client, '/api/remove-file', {'filename': 'demo'})
    assert res.status_code == 200
    assert not path.exists()


def test_rename_file(client, sandbox):
    write_demo(sandbox)
    res = post(client, '/api/rename-file', {'old': 'demo', 'new': 'demo2'})
    assert res.get_json()['ok'] is True
    assert not (sandbox / 'library' / 'demo.pyhol').exists()
    assert (sandbox / 'library' / 'demo2.pyhol').exists()


# ── check-modify ─────────────────────────────────────────────────

def test_check_modify_ok(client, sandbox):
    write_demo(sandbox)
    res = post(client, '/api/check-modify', {
        'filename': 'demo',
        'line_length': 80,
        'item': {'ty': 'thm.ax', 'name': 'another_ax',
                 'vars': {'A': 'bool'}, 'prop': 'A \u27f6 A'},
    })
    assert res.status_code == 200
    assert 'error' not in res.get_json()['item']


def test_check_modify_rejects_bad_term(client, sandbox):
    write_demo(sandbox)
    res = post(client, '/api/check-modify', {
        'filename': 'demo',
        'line_length': 80,
        'item': {'ty': 'thm.ax', 'name': 'bad_ax',
                 'vars': {'A': 'bool'}, 'prop': 'A \u27f6'},
    })
    assert res.status_code == 200
    assert 'error' in res.get_json()['item']


def test_check_modify_type_abbrev(client, sandbox):
    write_demo(sandbox)
    res = post(client, '/api/check-modify', {
        'filename': 'demo',
        'item': {'ty': 'type.abbrev', 'name': 'set3',
                 'args': ['a'], 'def': "'a \u21d2 bool"},
    })
    assert res.status_code == 200
    assert 'error' not in res.get_json()['item']


def test_check_modify_quotient(client, sandbox):
    write_demo(sandbox)
    # The relation must be annotated; the parentheses around `(t :: T)`
    # are required by the term grammar.  Arity is read off its tvars.
    res = post(client, '/api/check-modify', {
        'filename': 'demo',
        'item': {'ty': 'type.quot', 'name': 'q1', 'abs': 'mkq', 'rep': 'destq',
                 'rel': "(equals :: 'a \u21d2 'a \u21d2 bool)"},
    })
    item = res.get_json()['item']
    assert 'error' not in item
    assert item['args'] == ['a']
    assert item['abs'] == 'mkq' and item['rep'] == 'destq'


# ── theorem-search / theory-status ───────────────────────────────

def test_theorem_search(client):
    res = post(client, '/api/theorem-search', {
        'theory_name': 'logic_base', 'thm_name': '', 'pattern': 'conj',
    })
    names = [r['name'] for r in res.get_json()['results']]
    assert 'conjI' in names


def test_theory_status_after_validate(client, sandbox):
    write_demo(sandbox)
    res = post(client, '/api/validate-theory', {'filename': 'demo'})
    body = res.get_json()
    assert body['statuses']['self_imp'] == 'VALID'
    assert body['statuses']['my_ax'] == 'AXIOM'
    assert body['valid'] == 1 and body['axiom'] == 1
    status = client.get('/api/theory-status').get_json()
    assert status['self_imp'] == 'VALID'


def test_validate_theory_force(client, sandbox):
    write_demo(sandbox)
    post(client, '/api/validate-theory', {'filename': 'demo'})
    res = post(client, '/api/validate-theory',
               {'filename': 'demo', 'force': True})
    assert res.get_json()['statuses']['self_imp'] == 'VALID'


# ── v2 proof pipeline ────────────────────────────────────────────

def _init(client, prop='A \u27f6 A', theory_name='demo', vars={'A': 'bool'}):
    return post(client, '/api/v2/init-saved-proof', {
        'theory_name': theory_name, 'thm_name': '', 'vars': vars,
        'prop': prop, 'steps': [],
    })


def test_v2_init_saved_proof(client, sandbox):
    write_demo(sandbox)
    res = _init(client)
    assert res.status_code == 200
    state = res.get_json()['state']
    assert state['open_goals'] == [{'sid': 0, 'prop': 'A \u27f6 A'}]
    # method_direction covers every method the backend offers.
    assert set(state['method_direction']) == set(state['method_sig'])
    assert state['method_direction']['rule'] == ['backward']
    assert state['method_direction']['forward'] == ['forward']
    assert state['method_direction']['rewrite'] == ['backward', 'forward']
    assert state['method_direction']['cut'] == ['direct']


def test_v2_apply_method_closes(client, sandbox):
    write_demo(sandbox)
    res = post(client, '/api/v2/apply-method', {
        'theory_name': 'demo', 'thm_name': '', 'vars': {'A': 'bool'},
        'prop': 'A \u27f6 A', 'steps': [], 'index': 0,
        'step': {'method_name': 'intro', 'goal': 0},
    })
    body = res.get_json()
    assert res.status_code == 200
    assert body['num_gaps'] == 0
    assert [ni['sid'] for ni in body['new_items']] == [1]


def test_v2_apply_method_unknown_theorem_is_structured_error(client, sandbox):
    """The frontend reads response.data.error.err_type; a 500/string would
    make its error branch dead.  Regression guard for the 200+dict shape."""
    write_demo(sandbox)
    res = post(client, '/api/v2/apply-method', {
        'theory_name': 'demo', 'thm_name': '', 'vars': {'A': 'bool'},
        'prop': 'A \u27f6 A', 'steps': [], 'index': 0,
        'step': {'method_name': 'rule', 'goal': 0,
                 'theorem': 'nonexistent_thm_xyz'},
    })
    assert res.status_code == 200
    err = res.get_json()['error']
    assert err['err_type'] == 'TheoryException'
    assert 'nonexistent_thm_xyz' in err['err_str']


def test_v2_init_saved_proof_bad_prop_is_200_error(client, sandbox):
    write_demo(sandbox)
    res = _init(client, prop='A ==> A')  # old ASCII syntax: not parseable
    assert res.status_code == 200
    assert 'error' in res.get_json()


def test_v2_trust_report_reports_oracle(client, sandbox):
    """The interactive state carries no oracle report (compute_only skips
    the independent replay); trust-report pays for the full verify."""
    write_demo(sandbox)
    res = post(client, '/api/v2/apply-method', {
        'theory_name': 'demo', 'thm_name': '', 'vars': {'A': 'bool'},
        'prop': 'A \u27f6 A', 'steps': [], 'index': 0,
        'step': {'method_name': 'z3', 'goal': 0},
    })
    body = res.get_json()
    assert 'error' not in body
    steps = [{'method_name': 'z3', 'goal': 0,
              'new_ids': [ni['sid'] for ni in body['new_items']]}]
    report = post(client, '/api/v2/trust-report', {
        'theory_name': 'demo', 'thm_name': '', 'vars': {'A': 'bool'},
        'prop': 'A \u27f6 A', 'steps': steps, 'index': 1,
    }).get_json()
    assert report['oracles'] == ['z3']
    assert report['num_gaps'] == 0
    # An explicitly applied level-0 method self-authorizes (apply_macro
    # records the name), so even an empty trust list verifies it.
    strict = post(client, '/api/v2/trust-report', {
        'theory_name': 'demo', 'thm_name': '', 'vars': {'A': 'bool'},
        'prop': 'A \u27f6 A', 'steps': steps, 'index': 1, 'trust': [],
    }).get_json()
    assert strict['oracles'] == ['z3']


def test_v2_default_trust_admits_computation_oracles(client, sandbox):
    """Omitted trust -> COMPUTATION_ORACLES, so goals whose derivation
    folds constants (norm/auto -> *_eval) pass in the IDE."""
    state = _init(client, prop='(1::nat) + 1 = 2',
                  theory_name='nat', vars={}).get_json()['state']
    assert set(state['known_oracles']) == set(verify.COMPUTATION_ORACLES)
    assert set(state['trust']) == set(verify.COMPUTATION_ORACLES)
    res = post(client, '/api/v2/apply-method', {
        'theory_name': 'nat', 'thm_name': '', 'vars': {},
        'prop': '(1::nat) + 1 = 2', 'steps': [], 'index': 0,
        'step': {'method_name': 'auto', 'goal': 0},
    })
    body = res.get_json()
    assert 'error' not in body, body
    assert body['num_gaps'] == 0


# ── imperative + manual ──────────────────────────────────────────

def test_imp_list_and_load(client):
    listed = post(client, '/api/imp-list', {}).get_json()['files']
    assert listed, 'expected at least one .imp file'
    name = listed[0]['name']
    loaded = post(client, '/api/imp-load', {'name': name}).get_json()
    assert loaded['ok'] is True
    assert loaded['programs']


def test_imp_load_missing(client):
    res = post(client, '/api/imp-load', {'name': '__no_such_imp__'})
    assert res.get_json()['ok'] is False


def test_manual_list_and_load(client):
    listed = post(client, '/api/manual-list', {}).get_json()['files']
    names = [f['name'] for f in listed]
    assert names[0] == 'README'
    assert '07_system' in names
    loaded = post(client, '/api/manual-load', {'name': '07_system'}).get_json()
    assert loaded['ok'] is True
    assert '系统组织总览' in loaded['text']


def test_manual_load_missing(client):
    res = post(client, '/api/manual-load', {'name': '__nope__'})
    assert res.get_json()['ok'] is False
