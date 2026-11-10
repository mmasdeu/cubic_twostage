#!/usr/bin/env python3
"""Static and Lean-side checks for the Berend blueprint.

Run from any directory with the project root on LEAN_PATH. This generates only
scratch files under .scratch and never changes source or generated documentation.
"""
from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "blueprint" / "src" / "content.tex"
DOT = ROOT / "blueprint" / "dependency_graph.dot"
OUT = ROOT / ".scratch" / "blueprint-decls.lean"


def tex_names(value: str) -> list[str]:
    return [name.replace(":", "_").replace("-", "_") for name in re.split(r"\s*,\s*", re.sub(r"\s+", "", value.strip()))]


def main() -> int:
    tex = SRC.read_text()
    dot = DOT.read_text()
    labels = {label.replace(":", "_").replace("-", "_") for label in re.findall(r"\\label\{([^}]+)\}", tex)}
    lean_names: list[str] = []
    for group in re.findall(r"\\lean\{([^}]+)\}", tex):
        lean_names.extend(tex_names(group))
    uses: list[tuple[str, str]] = []
    current_label: str | None = None
    for match in re.finditer(r"\\(label|uses)\{([^}]+)\}", tex):
        kind, value = match.groups()
        if kind == "label":
            current_label = value.replace(":", "_").replace("-", "_")
        else:
            assert current_label is not None, "\\uses must occur in a statement/proof after a label"
            uses.extend((current_label, target) for target in tex_names(value))
    nodes = set(re.findall(r"^\s*([A-Za-z0-9_]+)\s*\[", dot, re.MULTILINE)) - {"graph", "node", "edge"}
    edges = set(re.findall(r"^\s*([A-Za-z0-9_]+)\s*->\s*([A-Za-z0-9_]+)", dot, re.MULTILINE))
    problems: list[str] = []
    for _source, target in uses:
        if target not in labels:
            problems.append(f"undefined LaTeX label: {target}")
        if target not in nodes:
            problems.append(f"node missing from dependency_graph.dot: {target}")
    for owner, dependency in uses:
        if (dependency, owner) not in edges:
            problems.append(f"edge missing from dependency_graph.dot: {dependency} -> {owner}")
    if labels - nodes:
        problems.append(f"theorems missing from dependency graph: {sorted(labels - nodes)}")
    if nodes - labels:
        problems.append(f"nodes without LaTeX statements: {sorted(nodes - labels)}")
    if problems:
        print("\n".join(problems), file=sys.stderr)
        return 1
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text("import CubicTwoStage\n" + "\n".join(f"#check {name}" for name in sorted(set(lean_names))) + "\n")
    if "--structure-only" in sys.argv:
        print(f"OK: {len(labels)} graph nodes and {len(edges)} DAG edges are consistent; Lean checks skipped (--structure-only)")
        return 0
    proc = subprocess.run(["lean", str(OUT)], cwd=ROOT)
    if proc.returncode:
        return proc.returncode
    print(f"OK: {len(set(lean_names))} Lean declarations exist; {len(labels)} graph nodes and {len(edges)} DAG edges are consistent")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
