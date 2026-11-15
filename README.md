# Free energy of bipartite random assignment — Lean companion

Machine-checked companion to Jacob Shkrob's
[*Thermodynamic limit of the bipartite random assignment problem*](https://github.com/shkroby/free-energy-assignment/blob/30a07cac13c213fe6337722b3626c411ff246eee/main.tex).
The model uses a square bipartite graph with an infinite array of iid
nonnegative costs, $F(s)\sim\kappa s^d$ at zero, and length scale
$(\kappa n)^{1/d}$. The Poisson tree uses independent rate-one exponential
spacings at each vertex, with cumulative spacings raised to $1/d$.

[FreeEnergy.lean](Certificate/FreeEnergy.lean) proves
`Certificate.freeEnergyClaim : Certificate.FreeEnergyClaim` with no local-limit
hypothesis. It establishes the Bethe pressure formula and almost-sure
convergence for every $d>0$ and inverse temperature $\beta>0$. A finite
positive-order cost moment gives eventual integrability and $L^1$ convergence.
[Model.lean](Certificate/Model.lean) gives the exact statement and
[MainReduction.lean](Certificate/MainReduction.lean) proves the hard cavity-law
existence and uniqueness assertion independently. The companion covers the
free-energy theorem. The manuscript's quenched overlap corollary is separate.

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
- **The multi-generation cutoff limit.** Lean counts all injective placements
  of a fixed plane shape with its children sorted by label. Conditional on
  each placement, the retained lengths have their iid product law. Their
  bounded continuous bracket test is exactly the original finite graph
  bracket on that event. The disjoint shape probabilities converge to the
  canonical Poisson probabilities, which sum to one. An auxiliary tree with
  independent cutoff lengths has the same bracket law as the canonical
  tree and gives the same shape mixture. Exchangeability identifies the
  expected bracket at any pinned root with the expected root average.
  See [FiniteLocalBracketLimit.lean](Certificate/FiniteLocalBracketLimit.lean),
  [IndependentShapeBracketMixture.lean](Certificate/IndependentShapeBracketMixture.lean),
  and [LocalRootSymmetry.lean](Certificate/LocalRootSymmetry.lean).
