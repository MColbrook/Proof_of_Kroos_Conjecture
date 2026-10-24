#!/usr/bin/env bash
# The protected Comparator configuration follows PalomarTemplate's current
# scripts/verify-comparator.sh (Apache-2.0), accessed 2026-10-24:
# https://github.com/PalomarRegistry/PalomarTemplate/blob/main/scripts/verify-comparator.sh
# Adapted for this complete development, audit, logs, and axiom reports.
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap lake lean python3 tee git; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required; use Linux with bubblewrap and the pinned Lean toolchain" >&2
    exit 1
  fi
done
python3 scripts/audit.py

prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: the selected toolchain does not bundle $tool" >&2
    exit 1
  fi
done

log_directory=".lake/verification/$(date -u +%Y%m%dT%H%M%SZ)"
mkdir -p "$log_directory"
python3 scripts/source_hashes.py --output "$log_directory/source-hashes.json"
cp comparator.json "$log_directory/submitted-comparator.json"
cp formalization.yaml "$log_directory/formalization.yaml"
config=$(mktemp "${TMPDIR:-/tmp}/bandlimited-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
from pathlib import Path
import sys

source, destination, prefix = sys.argv[1:]
config = json.loads(Path(source).read_text(encoding="utf-8"))
if "external_kernels" in config:
    raise SystemExit("external_kernels must not occur in submitted comparator.json")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

{
  printf 'UTC: %s\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
  printf 'Toolchain: %s\n' "$(cat lean-toolchain)"
  lean --version
  lake --version
  python3 --version
  printf 'Command: lake exe cache get\n'
  lake exe cache get
  printf 'Command: lake build\n'
  lake build
  printf 'Command: lake env lean AxiomReport.lean\n'
  lake env lean AxiomReport.lean
  printf 'Command: lake env lean NumericalBounds.lean\n'
  lake env lean NumericalBounds.lean
  printf 'Command: lake comparator --config <protected generated configuration>\n'
  lake comparator --config "$config"
  python3 scripts/source_hashes.py --check "$log_directory/source-hashes.json"
  printf 'Verification completed with Lean, NanoDa and con-ron.\n'
} 2>&1 | tee "$log_directory/verification.txt"

printf 'Verification log: %s/verification.txt\n' "$log_directory"
