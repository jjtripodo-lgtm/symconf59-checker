#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
stage="$(mktemp -d)"
trap 'rm -rf "$stage"' EXIT
(cd "$here"; sha256sum -c SOURCE_FULL_SHA256.txt > /dev/null)
cd "$stage"
export LEAN_PATH="$stage:${LEAN_PATH:?source pinned Lean/Mathlib environment first}"
lean --version
while IFS= read -r m; do
    mkdir -p "$(dirname "$m")"
    cp "$here/$m.lean" "$m.lean"
    lean -j1 -s65536 --trust=0 -DwarningAsError=true -o "$m.olean" "$m.lean"
    echo "PASS: $m, fresh trust-zero source"
done < "$here/FULL_ORDER.txt"
cp "$here/AuditFull.lean" .
lean -j1 -s65536 --trust=0 -DwarningAsError=true AuditFull.lean > audit_axioms.txt
cat audit_axioms.txt
python3 "$here/audit_axioms.py" audit_axioms.txt 19
echo "PASS: unrestricted 59_8, exact original incidence type"
