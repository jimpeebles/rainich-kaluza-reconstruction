# Adversarial review response and next-gate plan

Date: 2026-08-13

Status: **historical snapshot.**  The response and repairs below are
complete; Gates A--G are now tracked live in the gate crosswalk of
[`KALUZA_ARC_PLAN.md`](KALUZA_ARC_PLAN.md), which governs their current
status.  This file records the audit findings and repairs as of its date and
is no longer updated.

Original status: active response to the four repository-audit prompts
supplied after the high-level review

## 1. What was reviewed

The supplied text was a set of four detailed audit assignments rather than a
completed referee report.  We executed those assignments against the current
repository:

1. the actual-metric fourth-order detector spine;
2. the active finite metric-three-jet ambiguity;
3. the physical coupling channel and Kaluza reduction/uplift;
4. the exact Python/SymPy validation layer.

The audit was signature-level: definitions, theorem hypotheses, dependence on
actual Fréchet derivatives versus formal arrays, possible circularity,
non-vacuity, validation arithmetic, and artifact provenance were inspected.

## 2. Executive verdict

The central formal result survived the adversarial pass.

- The accepted detector is genuinely a function only of a coordinate metric
  field and a point.  Its derivatives are nested Mathlib `fderiv`
  constructions, not supplied formal fourth-jet arrays.
- The raw search is a finite filter over exactly (6{,}291{,}456) choices.
- Acceptance tests complete channel tensors and the full next-order residual;
  it is not a quotient that accepts by construction.
- The coupling (a) is absent from the detector definition.  It enters only
  the physical correctness theorems.
- The active common metric-three-jet family satisfies substantive truncated
  Einstein, Maxwell, scalar, Hodge, and first-Ricci-prolongation identities
  for every (a); its matter first jet is injective in (a).
- The polynomial metric realization uses genuine nested Fréchet derivatives.
- The five-dimensional Ricci blocks are derived from the Kaluza metric and
  Christoffel contractions; they are not definitions of EMD residuals.
- Validation uses exact symbolic/rational arithmetic for every scientific
  calculation.  No tolerance or floating-point decision enters a result.
- No `sorry`, `admit`, custom axiom, output-baking definition, or
  unsatisfiable universal-generic premise was found in the audited spine.

The review did identify real boundaries that must stay visible:

- compiled locality is equality of coordinate metric germs, not explicit
  four-jet extensionality and not nonlinear chart covariance;
- the abstract physical-patch and all-survivor theorems have strong,
  meaningful certificates but no concrete Lean inhabitant tying the full
  flagship patch to them;
- the structure named
  `ChoiceIndependentActualMetricEMDPhysicalPatch4` packages the Ricci,
  stress/Hodge, and two Maxwell exterior equations, not the scalar wave
  equation;
- the conditional uplift's `realize_emd` field already assumes that the
  realized fields satisfy EMD, and no concrete inhabitant of the full
  realizer interface is compiled;
- Lean verifies the convention-fixed Kaluza warp constants but does not prove
  them unique in a quantified general warp ansatz;
- the benchmark identifies its literal quotient derivative with physical
  (dA) through a compiled germ theorem plus the exact EMD patch, rather than
  an independent CAS expansion of the selected frame/channel second jet.

## 3. Repairs completed in this response

### 3.1 Active physical Maxwell potential jet

The previous claim ledger cited only the generic conditional theorem
`radialGaugePotentialTwoJet4_realizes`.  That was insufficient because the
active *rescaled* Maxwell first jet is not closed before unweighting.

The new module `ActiveAmbiguityPotentialTwoJet.lean` now:

- unweights the active rescaled jet with the exact product-rule term;
- proves closure of the normalized physical jet;
- restores the convention-registry physical Maxwell normalization;
- proves its alternation and closure;
- constructs compatible radial-gauge potential first- and second-derivative
  coefficient arrays;
- proves `activeAmbiguityPhysicalMaxwellPotentialTwoJet_realizes` for every
  coupling.

This is a finite point two-jet theorem, not an all-order field realization.

### 3.2 Exact detector search size

The new module `ActualMetricDetectorChoiceCount.lean` gives a transparent
product equivalence for every raw choice and proves

```text
allActualMetricDetectorChoices4.card = 6291456.
```

It also proves that the hand-written enumeration is the full finite universe
and restates accepted membership as the complete named metric-only predicate.

### 3.3 Validation provenance and tower scope

The validation language now says **128-slot exact quadratic quotient
representation**, not “128-dimensional number field.”  Valid square
relations certify zero identities; slot independence is not assumed.

The flagship artifact now records distinct hashes for:

- its human-readable input manifest;
- the complete symbolic metric/scalar/potential model;
- the relevant implementation sources;
- the quotient relations;
- the actual coefficient payload used by the tower calculation.

The custom algebra gains direct commutativity, associativity, distributivity,
embedding, and square-relation regressions.  The audit script rejects
approximate scientific APIs.  The selected source and active component now
have exact positive-square certificates; nonzero no longer follows from
treating a nonempty quotient coefficient vector as a proof of linear
independence.

### 3.4 Claim-boundary corrections

The canonical ledger, manuscript, supplement, roadmap, convention notes, and
validation guide now distinguish:

- Ricci--exterior EMD data from the full EMD equation set;
- fixed verified Kaluza constants from a uniqueness theorem;
- the conditional `realize_emd` handoff from a curvature-only uplift;
- germ locality from four-jet factorization;
- a 128-slot quotient computation from a proved degree-128 field.

## 4. Prioritized remaining plan

### Gate A — make “fourth order” a theorem about an explicit jet

Prove that equality of the coordinate metric value and derivatives through
order four at the point gives:

1. equality of every raw-choice acceptance predicate;
2. equality of the accepted finite sets;
3. equality of every raw-choice output.

Current germ extensionality is stronger as a hypothesis but weaker as an
order theorem.  This is the highest-value fully internal formalization gate.

### Gate B — compile one complete physical flagship instance

Build a concrete Lean inhabitant of the Ricci--exterior physical patch and
the selected/survivor certificates for an explicit model, preferably the
helical Kaluza patch.  A simpler exact analytic local model is acceptable as a
first non-vacuity witness.  This would convert the current exact symbolic
benchmark plus general Lean theorem into one machine-checked instance.

### Gate C — remove the last benchmark derivative mediation

Independently differentiate the literal selected quotient field, including
the selected coframe/channel second jet, and prove that its derivative equals
the physical (d(sqrt3 C)).  This is not needed for the general correctness
theorem, but it would make the flagship route a wholly direct exact
calculation.

### Gate D — simplify all-survivor correctness

Replace the per-survivor callback in the singleton theorem by one
choice-independent regular/simple-spectrum/unique-closure package that
constructs every survivor certificate.  In parallel, derive residual and
(q^2) regularity from ordinary (C^4) metric regularity on the separated
spectrum locus.

### Gate E — covariance

Prove a canonical correspondence of raw/accepted choices, or at least output
covariance, under the supported nonlinear coordinate-jet transformations.
Until then the publication term remains “fixed-coordinate finite detector.”

### Gate F — complete the Kaluza converse honestly

Replace `realize_emd` by lower-level reconstructed compatibility data and
derive the EMD equations.  Separately quantify a general warp ansatz and prove
the convention constants unique up to the stated sign/presentation
symmetries.  The existing Ricci reduction then supplies the nontrivial
EMD-to-vacuum implication.

### Gate G — external formal-PDE audit

The analytic solution-germ collision is conditional only on the explicit EMD
involutivity extension of Kruglikov's Einstein--Maxwell symbol complex by the
determined scalar-wave block.  Obtain a specialist sign-off or expand that
Spencer argument into a standalone proof.  This is the only headline gate
that cannot be closed by repository engineering alone.

## 5. Publication stop rule

Do not add another reconstruction layer or search for another exact solution
until Gates A--C or the external audit materially advance.  The paper should
lead with the exact shear-fiber classification, the active common
metric-three-jet collision, and one-order-higher coupling-square recovery.
Kaluza output (3) remains a necessary selector, not a converse recognition
criterion.
