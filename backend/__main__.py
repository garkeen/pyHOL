"""Run the pyHOL backend (Flask) standalone: `python -m backend`.

dev.ps1 starts the backend this way; the same app object is what
`backend/__init__.py` exports as `backend.app` (tests and WSGI servers
use that name directly).
"""

from backend import app

if __name__ == '__main__':
    app.run(host='127.0.0.1', port=5000, debug=True)
