# Research roadmap

This is the compact execution view.  The canonical operational plan is
[`docs/RESEARCH_PLAN.md`](docs/RESEARCH_PLAN.md); the paper-level claim boundary
is [`docs/CLAIM_LEDGER.md`](docs/CLAIM_LEDGER.md).

## North star

Publish a sharp local identifiability theorem for the EMD coupling magnitude
from the metric:

> After auditing the explicit EMD involutivity lemma, on an active, non-null,
> simple-spectrum analytic solution class,
> the metric three-jet cannot identify \(a^2\), while the physical
> curvature-normalized channel identifies \(a^2\) from one additional metric
> derivative.  A finite fourth-order coordinate detector realizes the positive
> direction under explicit entrance and survivor certificates.

This is the current paper.  A new closed-form spacetime, a global Kaluza
classification, and every degenerate branch are not required for publication.

## The theorem ladder

1. **Shear kernel -- proved in Lean.**  The complete first differentiated
   curvature-seed channels determine \((A,\eta)\), but not the hidden sine
   component \(B\).  The full tensors, not merely selected probes, are
   invariant under the one-parameter shear.
2. **Solution-level lower bound -- finite part in Lean, realization modulo one
   specialist-audit lemma.**  For every real \(a\), the repository constructs a
   complete compatible active EMD jet with one common metric three-jet, matter
   first jet injective in \(a\), and common simple real Ricci spectrum.  The
   written analytic realization argument uses the second-order potential
   variables \((g,A,\phi)\), Kruglikov's Theorem 3 plus Lemma 4, and EMD
   Noether/Bianchi compatibility.  Until its EMD involutivity lemma is audited,
   state the solution-germ theorem conditional on that lemma.
3. **Fourth-order recovery -- proved in Lean in the physical channel.**  On
   \(\eta\wedge Jv\ne0\), the constancy equation

   \[
     dA+2B\eta-B^2Jv=0
   \]

   gives a component-independent quotient for \(B\) and hence
   \(a^2=A^2+B^2\).
4. **Finite detector -- proved in Lean with stated hypotheses.**  The
   metric-only fourth-order accepted set is nonempty and contains the physical
   \(a^2\) on the packaged active-regular EMD locus.  Every survivor equals the
   physical value only with the displayed realized-branch, regularity, probe,
   and unique scalar-closure certificates.
5. **Kaluza selector -- necessary.**  Five-dimensional vacuum reduction fixes
   \(a^2=3\).  Detector output \(3\) is not by itself a converse uplift theorem.

## Publication gates

### Gate 1: formal-PDE specialist audit

- Check the potential-two-jet lift and the pure second-order
  \((g,A,\phi)\) formulation.
- Check that adding the determined scalar-wave block to Kruglikov's
  gauge-degenerate Einstein--Maxwell system preserves involutivity.
- Check the lower-order EMD terms and the Noether identity at the first
  compatibility order.
- Keep this step labeled as a human argument until independently reviewed; do
  not describe it as a direct application of Kruglikov's Theorem 4.

### Gate 2: positive benchmark completion

- At the committed generic helical-string point, evaluate the selected
  fourth-order frame/channel derivative.
- Route at least one exact physical choice through the complete detector and
  record output \(3\).
- Preserve the current fact: the earlier sample point fails the detector's
  causal scalar entrance, while the replacement point passes the pointwise
  upstream gates and physical active wedge.

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

Only after that should the project broaden to repeated-root, null-Maxwell,
null-scalar, or global/topological sectors.  Claims of genericity remain
openness claims unless density is separately proved, and the complete detector
remains fixed-coordinate until nonlinear chart covariance is established.

## Stop rules

- No new reconstruction machinery unless it closes one of the three
  publication gates.
- No new exact-solution search before the positive benchmark is complete.
- No degenerate-branch classification before the active paper is reviewable.
- No claim may exceed the evidence class recorded in the claim ledger.
