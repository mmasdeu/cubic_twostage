#!/usr/bin/env bash
# Elaborate the formalization against the Mathlib installed at /opt.
#
# Modules are built in dependency order (a module after the modules it imports),
# so a single run suffices on a clean tree, and the root module is built last.
set -euo pipefail
cd "$(dirname "$0")"
export LEAN_PATH="$PWD:$LEAN_PATH"

order=$(python3 - <<'PY'
import pathlib, re

files = sorted(pathlib.Path('CubicTwoStage').glob('*.lean'))
name = lambda p: 'CubicTwoStage.' + p.stem
deps = {}
for p in files:
    d = []
    for line in p.read_text().splitlines():
        m = re.match(r'\s*import\s+(CubicTwoStage\.\S+)', line)
        if m:
            d.append(m.group(1))
    deps[name(p)] = d

order, done, visiting = [], set(), set()

def visit(n):
    if n in done:
        return
    if n in visiting:
        raise SystemExit('import cycle at ' + n)
    visiting.add(n)
    for d in deps.get(n, []):
        visit(d)
    visiting.discard(n)
    done.add(n)
    order.append(n)

for n in sorted(deps):
    visit(n)
print('\n'.join(order))
PY
)

status=0
for mod in $order; do
  path="${mod//.//}"
  if ! lean -o "${path}.olean" -i "${path}.ilean" "${path}.lean"; then
    echo "FAILED: ${path}.lean"
    status=1
  else
    echo "ok: ${path}.lean"
  fi
done
if ! lean -o CubicTwoStage.olean CubicTwoStage.lean; then
  echo "FAILED: CubicTwoStage.lean"
  status=1
else
  echo "ok: CubicTwoStage.lean"
fi
exit $status
