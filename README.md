# Free energy of bipartite random assignment — Lean companion

Machine-checked companion to Jacob Shkrob's
[*Free energy of bipartite random assignment*](https://github.com/shkroby/free-energy-assignment/blob/c5eb385846e037630658169b0eb0db43da14976e/main.tex).
The model uses a square bipartite graph with an infinite array of iid
nonnegative costs, $F(s)\sim\kappa s^d$ at zero, and length scale
$(\kappa n)^{1/d}$. The Poisson tree uses independent rate-one exponential
spacings at each vertex, with cumulative spacings raised to $1/d$.

[MainReduction.lean](Certificate/MainReduction.lean) proves the hard
cavity-law assertion unconditionally and derives every conclusion in
`Certificate.FreeEnergyClaim` from one remaining input. That input is
convergence of the expected lower and upper vacancy brackets at each
fixed depth and integer length cutoff. The separate quenched overlap
theorem is outside this certificate's scope.

## Verify

Install [elan](https://leanprover-community.github.io/get_started.html) and run

```sh
lake exe cache get
bash scripts/check.sh
```

The repository pins Lean 4.33.0 and the matching mathlib release.
[Audit.lean](Audit.lean) checks transitive kernel axioms for all exported
certificate theorems. It accepts only `propext`, `Classical.choice`, and
`Quot.sound`. The check also rejects proof placeholders and new axiom
declarations. Explicit hypotheses remain visible in the theorem statements.

## Checked proof blocks

- **Weighted completion on the iid array.** The formal proof establishes
  logarithmic-cutoff expansion, short augmenting paths for every deficit,
  total insertion budgets, and the row-weight bound. The resulting
  measurable exceptional events have probability at most $4n^{-B}$
  eventually, for any fixed $B\ge 0$. This yields the deficit coefficient
  comparison and a uniform bound on negative pressure on the good events.
  See [CompletionExpansionFinal.lean](Certificate/CompletionExpansionFinal.lean).
- **Concentration, monomer removal, and the $L^1$ upgrade.** Independent
  rows give bounded differences for the actual partition function. The
  completion estimate transfers the soft limits to a finite hard limit.
  The positive pressure is uniformly $L^2$-bounded. The cyclic-assignment
  tail bound makes the negative pressure negligible on the exceptional
  events under the manuscript's positive-order moment assumption.
  See [SoftConcentrationLimit.lean](Certificate/SoftConcentrationLimit.lean),
  [CompletionTransfer.lean](Certificate/CompletionTransfer.lean),
  and [PressureL1.lean](Certificate/PressureL1.lean).
- **Canonical arrivals and the positive-fugacity formula.** The full
  marked Mecke identity holds on the exponential spacings for arbitrary
  iid measurable marks and tests of the retained configuration. Each
  measurable finite-intensity count has its exact Poisson law. Boundary
  cutoffs converge to the unique positive-fugacity law. The Bethe formula
  follows by differentiating the coupled tree messages, exchanging the
  signed endpoint contributions, and normalizing at large fugacity.
  See [PoissonArrivalMecke.lean](Certificate/PoissonArrivalMecke.lean),
  [PoissonArrivalCount.lean](Certificate/PoissonArrivalCount.lean),
  [SoftFixedPoint.lean](Certificate/SoftFixedPoint.lean), and
  [CanonicalBetheLimit.lean](Certificate/CanonicalBetheLimit.lean).
- **Hard cavity law and Bethe limit.** Logarithmic tail estimates give
  tightness and uniform second moments. Finite-prefix convergence and
  uniform control of omitted weights pass the limit through the full
  marked sum before inversion. The invariant hard coupling is constructed
  by monotone iteration from the common-quantile coupling, using weak
  compactness and closed lower-orthant order. Signed endpoint comparison
  and the strict countable probability-vector inequality identify the
  two marginals. Lean then verifies convergence of the full soft family
  and of the vertex and edge expectations in the Bethe formula.
  See [CanonicalHardExistence.lean](Certificate/CanonicalHardExistence.lean),
  [HardInvariantCoupling.lean](Certificate/HardInvariantCoupling.lean),
  and [CanonicalHardBethe.lean](Certificate/CanonicalHardBethe.lean).
- **Finite neighborhoods.** The one-root retained count and its
  conditional mark vector have the joint Poisson and iid mark limit.
  The fresh entries after a fixed exploration history retain their
  product law. Lean also verifies the labelled neighborhood cylinder
  probability, its per-placement asymptotics, the expected simple-path
  count, and the finite deletion bounds. Weighted isomorphism and
  continuity give the comparison of vacancy brackets on a fixed shape.
  See [LocalExplorationRetainedMarks.lean](Certificate/LocalExplorationRetainedMarks.lean),
  [LocalExplorationHistory.lean](Certificate/LocalExplorationHistory.lean),
  [LocalTreeShapeMass.lean](Certificate/LocalTreeShapeMass.lean),
  [LocalExplorationSize.lean](Certificate/LocalExplorationSize.lean),
  and [TreeBracketContinuity.lean](Certificate/TreeBracketContinuity.lean).

## Remaining proof

The multi-generation neighborhood argument still needs to identify the
weighted rooted shape distribution of the finite cutoff graph with its
canonical Poisson-tree limit. In particular, the labelled-placement
probabilities and test-function results need to be assembled into the
two expected bracket limits in
[freeEnergyClaim_of_cutoff_bracket_limits](Certificate/MainReduction.lean).
The unconditional proposition `Certificate.FreeEnergyClaim` remains
unproved in Lean.
