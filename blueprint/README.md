# Completed canonical Berend proof — Lean Blueprint

This directory follows the upstream [`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) layout.
The source is [`src/content.tex`](src/content.tex): each theorem-like item has a
fully qualified `\lean` declaration, a proof-status `\leanok` annotation, and
`\uses` links defining the dependency graph.

## Entry points

- [`src/web.tex`](src/web.tex): plasTeX web build, with `blueprint`'s
  `dep_graph` plugin and `plastexshowmore`.
- [`src/print.tex`](src/print.tex): the LaTeX companion for LuaLaTeX/pdfLaTeX.
- [`src/content.tex`](src/content.tex): the complete natural-language proof
  narrative, including normalized arc placement, both rate branches,
  Propositions 4.2 and 4.3, canonical B1, coprime IV.1, the full dichotomy,
  canonical Theorem 3.6, and the generic corrected introduction theorem.
- [`dependency_graph.dot`](dependency_graph.dot): the same proof DAG in
  Graphviz syntax. `dependency_graph.svg` is the rendered artifact.
- [`check_blueprint.py`](check_blueprint.py): checks labels, DAG edges, Lean
  declaration names, and that every blueprint item appears in the DAG.
- [`.github/workflows/blueprint.yml`](../.github/workflows/blueprint.yml):
  GitHub Actions configuration for declaration checks and both renderers.

## Meaning of the proof-status markers

`\leanok` marks declarations that are proved in the current root, not draft
work. The old false `berend_multi_invariance` axiom is gone. The canonical
Theorem 3.6 constructs the corrected proposition `H` using Stage I and coprime
Proposition IV.1; generic statements take `H` explicitly.

The only remaining custom axioms are `thm_main_computational_input` and
`thm_smooth_computational_input`, external computational data outside this
proof. An arbitrary-family corrected Berend theorem is not claimed separately.

## Rebuild locally

From the project root, first run

```sh
export LEAN_PATH="$PWD:$LEAN_PATH"
./check.sh
```

Use an isolated environment for Python dependencies (nothing global is
installed):

```sh
python3 -m venv .scratch/blueprint-venv
.scratch/blueprint-venv/bin/pip install -r blueprint/requirements.txt
python3 blueprint/check_blueprint.py
```

Render the LaTeX companion and Graphviz graph with

```sh
cd blueprint/src && latexmk -r latexmkrc print.tex
dot -Tsvg blueprint/dependency_graph.dot -o blueprint/dependency_graph.svg
```

For the web version, use the local plugin:

```sh
cd blueprint/src
../../.scratch/blueprint-venv/bin/plastex --config plastex.cfg web.tex
```

This writes `blueprint/web/`. The plugin creates its dependency graph from the
LaTeX labels; the checked-in DOT/SVG graph is independently verified by the
script to contain the same nodes and edges.

The original upstream template and macro conventions are at
https://github.com/PatrickMassot/leanblueprint . The GitHub workflow builds all three renderings and publishes the assembled
static site to GitHub Pages when it runs on `main` (or by manual dispatch).
The project page is `https://mmasdeu.github.io/cubic_twostage/`. A first-time
push to a new branch alone is not evidence that pages deployment has completed.
