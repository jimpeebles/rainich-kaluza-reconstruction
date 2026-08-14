# Research roadmap

This is the compact execution view.  The canonical operational plan is
[`docs/RESEARCH_PLAN.md`](docs/RESEARCH_PLAN.md); the paper-level claim boundary
is [`docs/CLAIM_LEDGER.md`](docs/CLAIM_LEDGER.md).

## North star

Publish a sharp local identifiability theorem for the EMD coupling magnitude
from the metric:

> After specialist audit of the external-theorem-dependent EMD involutivity
> proposition, on an active, non-null, simple-spectrum analytic solution class,
> the metric three-jet cannot identify \(a^2\), while the physical
> curvature-normalized channel identifies \(a^2\) from one additional metric
> derivative.  A finite fourth-order coordinate detector realizes the positive
> direction under explicit entrance and survivor certificates.

This is the current paper.  A new closed-form spacetime, a global Kaluza
classification, and every degenerate branch are not required for publication.

## The theorem ladder

1. **Exact order-three fiber -- proved in Lean.**  When the seed amplitude and
   scalar covector are nonzero, two complete first differentiated
   curvature-seed channel inputs agree exactly when their \(A\) values agree
   and their \((d\theta,B)\) data lie on one unique affine real-shear orbit.
   The full tensors, not merely selected probes, have an \(\mathbb R\)-fiber.
2. **Solution-level lower bound -- finite part in Lean, proposition-level
   realization pending specialist audit.**  For every real \(a\), the repository constructs a
   displayed compatible active truncated EMD jet with one common metric three-jet, matter
   first jet injective in \(a\), and common simple real Ricci spectrum.  The
   correctly unweighted physical Maxwell first jet is now proved closed and
   is realized by an actual quadratic radial-gauge potential with genuine
   nested first and second Fréchet derivatives for every coupling.  The
   proposition-level analytic realization argument uses the second-order potential
   variables \((g,A,\phi)\), Kruglikov's Theorem 3 plus Lemma 4, and EMD
   Noether/Bianchi compatibility.  An exact rational certificate reproduces
   the predicted Cartan characters \((60,45,25,5)\),
   \(\dim g_2=135\), \(\dim g_3=245\), Hilbert growth through \(g_5\), and
   syzygy exhaustion through that tested range.  It also extracts the full
   coordinate residual's 150-column highest-jet Jacobian at the active lower
   jet, matches the hand-built symbol entrywise for symbolic \(a\), and finds
   rank 15.  It does not certify lower-order Noether torsion, prolonged
   nonlinear regularity, all-order formal integrability, or realization.  Until
   the EMD proposition is independently audited, state the solution-germ
   theorem as external-theorem dependent and pending that audit.
3. **Fourth-order recovery -- proved in Lean in the physical channel.**  On
   \(\eta\wedge Jv\ne0\), the constancy equation

   \[
     dA+2B\eta-B^2Jv=0
   \]

   gives a component-independent quotient for \(B\) and hence
   \(a^2=A^2+B^2\).  On the explicit active formal family, two fixed
   fourth-order outputs agree iff \(a=\pm b\): the order-three \(\mathbb R\)
   ambiguity collapses exactly to the orientation-free \(\mathbb Z_2\).
4. **Finite detector -- proved in Lean with stated hypotheses; primitive
   four-jet factorization partially closed.**  The
   exact raw search has \(6{,}291{,}456\) choices.  The metric-only
   fourth-order accepted set is nonempty and contains the physical
   \(a^2\) on the packaged active-regular Ricci--exterior EMD locus.  Every survivor equals the
   physical value only with the displayed realized-branch, regularity, probe,
   and unique scalar-closure certificates.  The algebraic entrance factors
   through the metric two-jet and the channel factors through a finite
   operational first-jet payload.  The genuine matrix-inverse chain rule and
   actual composed-Ricci one-jet factorization are compiled.  What remains is
   the downstream chain-rule bridge showing that the literal metric four-jet
   determines the full upstream entrance and the rest of that payload.
5. **Kaluza selector -- necessary.**  For the convention-fixed warp constants,
   five-dimensional vacuum reduction verifies \(a^2=3\).  Lean does not yet
   prove those constants unique in a general warp family.  Detector output
   \(3\) is not by itself a converse uplift theorem.

## Publication gates

### Gate 1: formal-PDE specialist audit

- Check the actual quadratic potential lift and the pure second-order
  \((g,A,\phi)\) formulation.
- Audit the proposition-level direct-sum argument against Kruglikov's Spencer
  complex and the exact-rational characters \((60,45,25,5)\).
- Check that the Maxwell gauge identity and EMD Noether/Bianchi identity
  exhaust the complete first compatibility space, and that regularity plus
  Cartan--Kähler gives the prescribed-jet conclusion.
- Keep this step labeled as a human argument until independently reviewed; do
  not describe it as a direct application of Kruglikov's Theorem 4.

### Gate 2: positive benchmark completion -- closed

- The replacement helical-string point passes 21 exact checks through the
  selected scalar/residual/frame one-jets, all 128 complete-channel
  components, \(A\), physical \(dA=d(\sqrt3 C)\), \(B\), the full next-order
  residual, and output \(3\).  The custom calculation uses a 128-slot exact
  quadratic quotient representation; it does not claim a degree-128
  number-field basis.  Model, implementation, relation, and coefficient
  payload hashes are recorded separately.
- The literal quotient-derivative equality is supplied by the compiled
  physical-germ bridge composed with the exact helical Kaluza EMD patch/open
  gates.  This is theorem-mediated exact evidence, not a brute-force
  second-jet CAS expansion or a benchmark-specific Lean theorem instance.
- The earlier sample point still fails the detector's causal scalar entrance;
  the replacement point is the positive route.

### Gate 3: paper hardening

- Obtain formal-PDE, Rainich/EMD, and relativity reviews.
- Make every headline sentence trace to the claim ledger.
- Run the Lean axiom audit and exact-symbolic validation from clean state.
- Freeze the terminology: “metric-three-jet non-identifiability,” “physical
  fourth-order channel recovery,” and “finite coordinate detector.”

## After the paper

The next landmark is a converse on the reconstructed branch.  After recovering
\(B\), study

\[
  dB=2A\left(\eta-\frac B2Jv\right),\qquad d(A^2+B^2)=0,
\]

then integrate the scalar and Maxwell data and connect the accepted branch to
the existing conditional Kaluza uplift module.  Directly differentiating the
quotient for \(B\) may require a metric five-jet.

The current uplift realizer already assumes the complete EMD equations, and
the detector's strongest abstract physical/survivor packages have no concrete
Lean inhabitant.  Replacing those handoffs with lower-level derived data,
closing the remaining metric-four-jet-to-upstream-and-operational-jet
chain-rule seams, and
then proving chart covariance are the next formalization gates.

Only after that should the project broaden to repeated-root, null-Maxwell,
null-scalar, or global/topological sectors.  Claims of genericity remain
openness claims unless density is separately proved, and the complete detector
remains fixed-coordinate until nonlinear chart covariance is established.

## Stop rules

- No new reconstruction machinery unless it closes one of the three
  publication gates.
- No new exact-solution search before the analytic audit and paper hardening
  are complete.
- No degenerate-branch classification before the active paper is reviewable.
- No claim may exceed the evidence class recorded in the claim ledger.
