"""Setup flask app."""

from flask import Flask
from flask.json.provider import DefaultJSONProvider
from flask_cors import CORS


class JSONProvider(DefaultJSONProvider):
    """Custom JSON provider to handle special types."""
    def default(self, o):
        if hasattr(o, 'keys') and hasattr(o, '__getitem__'):
            return dict(o)
        return super().default(o)


def create_app():
    """Create and configure the Flask application."""
    app = Flask(__name__, static_url_path='/static')
    app.json_provider_class = JSONProvider
    app.json = JSONProvider(app)
    CORS(app, resources={r"/api/*": {"origins": "*"}})
    app.secret_key = b'_5#y2L"F4Q8z\n\xec]/'
    return app


app = create_app()
