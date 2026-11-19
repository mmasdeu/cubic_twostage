# Sphinx configuration of the cubic_twostage documentation.
# Build with `make html` in this directory (the package and Sage must be importable).

# -- General configuration ------------------------------------------------
extensions = [
    "sphinx.ext.autodoc",
    "sphinx.ext.todo",
    "sphinx.ext.mathjax",
    "sphinx.ext.viewcode",
    "sphinx.ext.intersphinx",
]

# Sage docstrings use `...` for math (Sage convention)
default_role = "math"

source_suffix = ".rst"
master_doc = "index"

project = "cubic_twostage"
copyright = "2026, Marc Masdeu"
package_name = "cubic_twostage"
project_description = (
    "Certified 2-stage Euclidean coverings and continued fractions in number fields"
)
authors = "Marc Masdeu"

# The version info for the project you're documenting, acts as replacement for
# |version| and |release|.
release = "1.0"

exclude_patterns = ["_build", "news", "strategy_outline.md"]

intersphinx_mapping = {"sage": ("https://doc.sagemath.org/html/en/reference", None)}

autodoc_member_order = "bysource"

# -- Options for HTML output ----------------------------------------------
try:
    import furo  # noqa: F401

    html_theme = "furo"
except ImportError:
    html_theme = "alabaster"
html_static_path = ["static"]
htmlhelp_basename = project

# -- Options for LaTeX output ---------------------------------------------
latex_elements = {}
latex_documents = [
    ("index", project + ".tex", package_name + " Documentation", authors, "manual"),
]

# The docstrings of the witness modules are plain text (with |...| for norms, which reST would
# read as substitutions): show them as preformatted blocks.
PLAIN_TEXT_MODULES = (
    "cubic_twostage.witness_orbit",
    "cubic_twostage.certify_lower",
    "cubic_twostage.witness_fast",
)


def _plain_docstrings(app, what, name, obj, options, lines):
    if name.startswith(PLAIN_TEXT_MODULES) and any(l.strip() for l in lines):
        lines[:] = ["::", ""] + ["    " + l for l in lines] + [""]


def setup(app):
    app.connect("autodoc-process-docstring", _plain_docstrings)
