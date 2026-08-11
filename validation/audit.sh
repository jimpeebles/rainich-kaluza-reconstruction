#!/usr/bin/env bash
set -euo pipefail

validation_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$validation_root"

uv sync --frozen
uv run --frozen python -m unittest discover -s tests -v
uv run --frozen python -m benchmarks.vt1_flat_pure_gauge --check
