#!/usr/bin/env bash
set -euo pipefail

validation_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$validation_root"

uv sync --frozen
if rg -n --glob '*.py' --glob '!no_approx.py' \
  '\bevalf\b|\bnsimplify\b|\bisclose\b|\bnumpy\b|sp\.Float|[0-9]+(?:\.[0-9]+)?[eE]-[0-9]+' \
  rk_validation benchmarks tests; then
  echo "prohibited approximate scientific arithmetic found" >&2
  exit 1
fi
uv run --frozen python -m rk_validation.no_approx
uv run --frozen python -m unittest discover -s tests -v
uv run --frozen python -m benchmarks.vt1_flat_pure_gauge --check
uv run --frozen python -m benchmarks.vt1b_boosted_black_string --check
uv run --frozen python -m benchmarks.vt1c_non_kaluza_dilaton --check
uv run --frozen python -m benchmarks.vt2_generic_helical_string --check
uv run --frozen python -m benchmarks.vt2_complete_detector_route --check
uv run --frozen python -m benchmarks.vt2b_generic_near_miss --check
uv run --frozen python -m benchmarks.vt3_emd_symbol_involutivity --check
