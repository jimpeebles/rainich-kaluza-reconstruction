#!/usr/bin/env bash
set -euo pipefail

validation_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$validation_root"

uv sync --frozen
uv run --frozen python -m unittest discover -s tests -v
uv run --frozen python -m benchmarks.vt1_flat_pure_gauge --check
uv run --frozen python -m benchmarks.vt1b_boosted_black_string --check
uv run --frozen python -m benchmarks.vt1c_non_kaluza_dilaton --check
uv run --frozen python -m benchmarks.vt2_generic_helical_string --check
uv run --frozen python -m benchmarks.vt2_complete_detector_route --check
uv run --frozen python -m benchmarks.vt2b_generic_near_miss --check
