# Phase-V exact-metric validation harness

This directory is the reproducible computational-evidence layer for canonical
Phase V. It is intentionally separate from `RainichKaluza/`: a passing
benchmark here is exact symbolic evidence, not a Lean proof and not a
substitute for any Phase-II or Phase-IV theorem gate.

## Reproduce

From this directory, with `uv` installed:

```sh
uv sync --frozen
uv run python -m unittest discover -s tests -v
uv run python -m benchmarks.vt1_flat_pure_gauge
uv run python -m benchmarks.vt1_flat_pure_gauge --check
```

The Python minor line and SymPy release are fixed in `pyproject.toml`; exact
resolved package hashes are recorded in `uv.lock`. Benchmark artifacts record
the runtime versions, canonicalized inputs, SHA-256 input identity, individual
checks, and residual hashes. No benchmark uses floating-point arithmetic.
The final `--check` command fails if fresh exact output differs byte-for-byte
from the committed artifact. `./audit.sh` runs the entire validation sequence.

## V-T1 seed benchmark

`vt1-flat-cylindrical-pure-gauge` begins the infrastructure with a deliberately
simple but nontrivial oracle:

- four-dimensional Minkowski space is expressed in cylindrical coordinates,
  so the Christoffel symbols are nonzero while the Ricci tensor vanishes;
- `A = d(r y)` is nonzero but has exactly vanishing field strength;
- the convention-fixed EMD residuals vanish at `a = sqrt(3)`;
- the Kaluza uplift is matched componentwise to the pullback under
  `z' = z + r y` and has nonzero Christoffel symbols but zero Ricci tensor.

This tests nonlinear coordinate covariance, the local gauge-coordinate law,
the uplift constants, and the zero-residual contract before larger exact
solutions are introduced.

## Evidence policy

Committed JSON files in `artifacts/` are generated outputs. A change is
accepted only when rerunning the named benchmark reproduces the artifact
byte-for-byte. Each future exact solution must also provide:

1. a source and explicit map from source conventions to repository
   conventions;
2. a human-readable input specification;
3. exact residual checks (or documented certified bounds when exact reduction
   is impossible);
4. a named expected branch or rejection outcome;
5. tests that fail if the expected classification changes.
