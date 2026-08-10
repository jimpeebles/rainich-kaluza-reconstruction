#!/usr/bin/env bash
set -euo pipefail

if rg -n '^\s*(sorry|admit|axiom)\b' RainichKaluza RainichKaluza.lean; then
  echo "Forbidden placeholder or project axiom found in Lean source." >&2
  exit 1
fi

lake build --wfail
lake env lean RainichKaluza/AxiomAudit.lean
