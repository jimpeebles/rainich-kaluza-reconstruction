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
uv run python -m benchmarks.vt1b_boosted_black_string
uv run python -m benchmarks.vt1b_boosted_black_string --check
uv run python -m benchmarks.vt1c_non_kaluza_dilaton
uv run python -m benchmarks.vt1c_non_kaluza_dilaton --check
uv run python -m benchmarks.vt2_generic_helical_string
uv run python -m benchmarks.vt2_generic_helical_string --check
uv run python -m benchmarks.vt2_complete_detector_route
uv run python -m benchmarks.vt2_complete_detector_route --check
uv run python -m benchmarks.vt2b_generic_near_miss
uv run python -m benchmarks.vt2b_generic_near_miss --check
uv run python -m benchmarks.vt3_emd_symbol_involutivity
uv run python -m benchmarks.vt3_emd_symbol_involutivity --check
```

The Python minor line and SymPy release are fixed in `pyproject.toml`; exact
resolved package hashes are recorded in `uv.lock`. Benchmark artifacts record
the runtime versions, a SHA-256 identity for the declared human-readable input
manifest, individual checks, and residual hashes.  That manifest hash is not a
hash of the implementation or every symbolic expression.  The flagship route
therefore also records separate hashes of its complete symbolic model, the
relevant implementation sources and lockfiles, the source benchmark and its
artifact, its quotient relations, and its coefficient payload. No benchmark
uses floating-point scientific arithmetic. The final `--check` command fails
if fresh exact output differs byte-for-byte from the committed artifact.
`./audit.sh` also rejects floating-point literals and common approximate
numerical APIs/imports before running the entire validation sequence.

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

## V-T1b convention-ladder benchmark

`vt1b-boosted-black-string` starts from the exact Ricci-flat product of
four-dimensional Schwarzschild with a flat fifth direction, performs a
Lorentz boost mixing time and the Kaluza coordinate, and reduces along the
boosted circle. The four-dimensional fields have nonzero scalar gradient,
nonzero electric Maxwell field, and nonzero Ricci curvature. Eight exact
checks verify the `a=sqrt(3)` EMD equations, equality of the uplift with the
boosted black string, five-dimensional Ricci-flatness, the necessary Kaluza
polynomial obstruction, and honest routing to the repeated-Ricci-root branch;
a ninth reconstructs `aGeomSq=3` from the active Hodge-dual differential
channel of the exponentially rescaled Maxwell field. The omitted constant
`1/√2` curvature normalization cancels from the ratio. It is a substantive
convention and coupling-channel test but not the required generic rotating
dyonic benchmark.

## V-T1c non-Kaluza EMD control

`vt1c-non-kaluza-dilaton` maps the exact static electric
Gibbons--Maeda--Garfinkle--Horowitz--Strominger black hole into the repository
normalization at `a=1`. Nine exact checks show that its scalar, Maxwell, and
Ricci sectors are nonzero; the full EMD residual vanishes; the active
Hodge-dual channel reconstructs `aGeomSq=1`; and the Kaluza selector rejects
it. Its convention-fixed Kaluza uplift is correspondingly not Ricci-flat.
The purely algebraic Kaluza polynomial obstruction nevertheless vanishes,
giving a useful exact demonstration that differential coupling recovery adds
selectivity. Spherical symmetry again places this control on the repeated-root
branch, so a generic non-Kaluza control is still required.

## V-T2 generic positive benchmark

`vt2-generic-helical-string` applies both a time/fiber boost and an
azimuthal/fiber twist to the exact Schwarzschild black string, then reduces
along the resulting spacelike helical Killing direction. The uplift identity
and reference five-dimensional vacuum equation are checked symbolically. At
the exact point `r=3, theta=pi/4`, a two-jet evaluator checks the full EMD
residual without floating-point arithmetic. The scalar and Maxwell sectors are
nonnull, the mixed Ricci tensor has four distinct real roots and nonzero
characteristic discriminant, and the active primal differential channel
reconstructs `aGeomSq=3`. This is an exact positive oracle for the physical
EMD and differential-channel equations on a real simple-spectrum point. It is
not a positive oracle for the complete finite detector: the literal lower
complementary eigenspace at the committed point is spacelike, so the detector's
fixed timelike scalar-amplitude gate fails.

## V-T2 complete-detector routing audit

`vt2-complete-detector-route` evaluates the literal spectral ordering and
scalar entrance used by the Lean detector. At the committed point
`r=3, theta=pi/4`, the algebraic point gates pass but
`-2 reconstructedDiagonalA < 0`; because this conjunct is independent of all
6,291,456 raw finite choices, the accepted set is exactly empty there. This
coexists consistently with the independent physical channel returning `3`:
the point lies outside the detector's stated causal branch.

The same artifact tests `r=3/2, theta=pi/4`. There the algebraic and both
scalar-radicand gates pass; probes `(1,2)` have the required causal signs; and
the literal `relativeMinus=false` scalar candidate equals the exact physical
`dphi`. Exact differentiation of the literal roots, four-root projectors,
normalizations, and amplitudes also reduces its complete scalar-closure
obstruction to zero. Its reconstruction obstruction and all six Maxwell
residual/projector identities vanish exactly. A literal finite frame choice
uses minus probes `(0,1)` with pivot recipe `second`, plus probes `(0,1)`, and
`orientationReverse=true`; all four strict signs pass, its frame determinant
is `-16 sqrt(249)/747`, its oriented coframe determinant is
`3 sqrt(249)/16 > 0`, and the coordinate-metric Hodge equality is exact.
Finally, a convention-aligned physical Maxwell/Hodge calculation agrees with
the detector residual and gives the choice-free active component
`(omega wedge S^T dphi)_(1,2) = 1486879232 sqrt(3)/30795876033 != 0`.

The last finite calculation is performed in an explicit 128-slot square-free
quadratic quotient representation. Valid square-relation reductions certify
its zero identities; the code does not claim that all 128 slots are linearly
independent over the rationals. Direct ring-law regressions and committed
relation/coefficient hashes protect the custom algebra implementation.
The selected source and active component have independent exact
positive-square certificates, avoiding any inference from slot-vector
nonemptiness. Together with the physical-activity/invertible-channel bridge,
the calculation certifies the literal selected scalar and Maxwell-residual
one-jets, the selected frame/coframe one-jet, all 128 components of the two
complete first-order seed channels, source component `0`, active wedge
component `(0,3)`, and the literal cosine quotient
`A=5 sqrt(53859)/17953`. Independently, exact differentiation of the physical
complexion gives

`d(sqrt(3) C) = (0, -3999888 sqrt(53859)/322310209,
5869152 sqrt(53859)/322310209, 0)`.

With this physical `dA`, the sine quotient is
`B=18 sqrt(2980198)/17953`, all four next-order residuals vanish, and
`A^2+B^2=3` exactly.

There are two evidence layers. The JSON artifact directly certifies the exact
point/tower statements above. Identifying physical `dA` with the derivative
of the detector's literal quotient *field* is theorem-mediated: the exact
helical uplift supplies the local constant-coupling EMD germ, the strict
finite gates persist on a neighborhood, and the compiled physical-germ bridge
then identifies the quotient field and derivative. The artifact does not
independently expand the selected frame/channel second jet, and it is not a
Lean instance theorem or a general complete-detector theorem.

## V-T2b generic near miss

`vt2b-generic-near-miss` changes only the `tt` second jet of V-T2 by adding
`(r-3)^2/100`. At the exact test point, the metric value and complete first jet
are therefore identical to the genuine Kaluza solution, while the controlled
second derivative is nonzero. The perturbed metric remains Lorentzian and its
mixed Ricci tensor still has four distinct real roots, but the named Kaluza
polynomial obstruction becomes nonzero and the original EMD fields no longer
solve the Einstein equation. This supplies a close, generic, exact non-EMD
rejection rather than an obviously unrelated counterexample.

## V-T3 EMD potential-symbol involutivity certificate

`vt3-emd-symbol-involutivity` builds the exact rational principal symbol of
the pure second-order potential-form EMD system at a Lorentzian normal-frame
point.  It checks the linearized-Ricci, Maxwell `div d`, and scalar-wave
blocks separately and as a direct sum.  Exact row reduction gives Cartan
characters

```text
Einstein/Ricci       (40, 30, 16, 4)
Maxwell potential    (16, 12,  7, 1)
scalar wave           (4,  3,  2, 0)
EMD total            (60, 45, 25, 5)
```

and dimensions `dim g2=135`, `dim g3=245`.  The committed certificate also
checks the Cartan/Hilbert growth through `g5`, verifies that the four
contracted-Bianchi plus one Maxwell-gauge syzygies annihilate and exhaust the
tested symbol left kernels.  On four selected non-null covectors the symbol
kernel is exactly the explicit five-dimensional gauge image; two selected
null covectors exhibit the expected additional characteristic kernel.  The
artifact does not itself prove the corresponding statement on every Lorentz
orbit.

As an independent modeling check, the benchmark also extracts all 150
highest-jet Jacobian columns from the full coordinate EMD residual evaluator
at the repository's active lower jet, with the coupling retained as a symbolic
real parameter.  This coordinate Jacobian equals the hand-built block symbol
entry-for-entry and has rank 15, certifying that the second-order equation map
is a submersion in its highest-jet directions at that witness.  The evaluator
uses the trace-reversed Ricci form of the metric equation; in four dimensions
this differs from the Einstein-tensor form by an invertible target trace
reversal and has the same regularity and solution set.

This is an exact principal-symbol/Cartan certificate, not by itself a proof
of nonlinear formal integrability.  It does not certify the lower-order
Noether compatibility, all prolonged nonlinear regularity, or analytic
Cartan--Kähler realization.  Those steps are stated separately in
`docs/ANALYTIC_EMD_REALIZATION.md` and remain the point for specialist audit.

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
