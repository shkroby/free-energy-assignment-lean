# Free energy of bipartite random assignment — Lean companion

This repository contains a partial machine-checked certificate for Jacob
Shkrob's [*Free energy of bipartite random assignment*](https://github.com/shkroby/free-energy-assignment/blob/c5eb385846e037630658169b0eb0db43da14976e/main.tex).
[Model.lean](Certificate/Model.lean) states the almost-sure pressure limit,
the additional $L^1$ conclusion under a cost moment, and the zero-fugacity
cavity-law and Bethe formula assertions. A proof of the combined
`Certificate.FreeEnergyClaim` remains open in Lean. The separate quenched
overlap theorem is outside this certificate's scope.

The model uses a complete square bipartite graph, a single infinite array
of iid nonnegative costs, $F(s)\sim \kappa s^d$ at zero, and the length
scale $(\kappa n)^{1/d}$. The Poisson tree uses rate-one exponential spacings
at each vertex, with cumulative spacings raised to $1/d$.

## Verify

Install [elan](https://leanprover-community.github.io/get_started.html) and run

```sh
lake exe cache get
bash scripts/check.sh
```

The repository pins Lean 4.33.0 and the matching mathlib release.
[Audit.lean](Audit.lean) checks all exported certificate theorems for
transitive kernel axioms. It accepts `propext`, `Classical.choice`, and
`Quot.sound`. The check also rejects proof placeholders and new axiom
declarations. Explicit theorem hypotheses are visible in their signatures.

## Checked proof blocks

- **Weighted completion on the iid array.** The formal proof establishes
  logarithmic-cutoff expansion, short augmenting paths for every deficit,
  total edge and length budgets, and a row-weight bound. The resulting
  measurable exceptional events have probability at most $4n^{-B}$
  eventually, for any fixed $B\ge 0$. The certificate gives the deficit
  coefficient comparison and a bound on the negative pressure on the good
  events. See [CompletionExpansionFinal.lean](Certificate/CompletionExpansionFinal.lean).
- **Removing monomers and upgrading convergence.** The convergence of
  deterministic positive-fugacity pressure limits implies existence of
  a finite hard limit and almost-sure convergence to it. The row-weight
  second-moment estimate and the cyclic-assignment negative-tail estimate
  then yield the manuscript's $L^1$ conclusion. Both limits follow from
  the stated local-vacancy convergence hypothesis.
  See [PressureFromLocal.lean](Certificate/PressureFromLocal.lean),
  [CompletionTransfer.lean](Certificate/CompletionTransfer.lean), and
  [PressureL1.lean](Certificate/PressureL1.lean).
- **Finite monomer pressure.** The finite deletion identity gives the
  logarithmic derivative and integral formula, and iterated deletion gives
  rigorous bounds at every depth. Expected long-edge weights control the
  pressure cutoff uniformly in graph size. Independent rows give the
  bounded-differences estimate and almost-sure concentration for the actual
  cost array.
  See [FiniteRootBounds.lean](Certificate/FiniteRootBounds.lean),
  [SoftExpected.lean](Certificate/SoftExpected.lean),
  [SoftAssignment.lean](Certificate/SoftAssignment.lean), and
  [SoftConcentrationLimit.lean](Certificate/SoftConcentrationLimit.lean).
- **One-step neighborhood laws.** Retained labels and marks have an exact
  product formula. Exposing a fixed finite collection of row and column
  roots with connecting entries deleted gives independent counts whose
  joint point probabilities converge to those of independent Poisson counts.
  See [LocalExplorationPattern.lean](Certificate/LocalExplorationPattern.lean)
  and [LocalExplorationLimits.lean](Certificate/LocalExplorationLimits.lean).
- **Canonical marked arrivals.** The full Mecke insertion identity holds
  for any iid measurable mark law and nonnegative measurable test of the
  selected point and the remaining configuration. Each measurable
  finite-intensity count has its exact Poisson law. The same arrival model
  supports the stretched-log-tail series criterion and omitted-weight
  probability bound. See
  [PoissonArrivalMecke.lean](Certificate/PoissonArrivalMecke.lean),
  [PoissonArrivalCount.lean](Certificate/PoissonArrivalCount.lean),
  [ArrivalTails.lean](Certificate/ArrivalTails.lean), and
  [ArrivalTruncation.lean](Certificate/ArrivalTruncation.lean).
- **Tree messages with monomers.** The canonical tree has iid independent
  root branches and summable outgoing weights. Its extremal boundary
  sequences satisfy the crossed laws, and the marked insertion identity
  forces their limits to agree. The resulting canonical root law is the
  unique bounded positive-fugacity fixed point. The cutoff root messages
  converge to it almost surely and in expectation.
  See [SoftFixedPoint.lean](Certificate/SoftFixedPoint.lean) and
  [CanonicalCutoffLimit.lean](Certificate/CanonicalCutoffLimit.lean).
- **Zero-fugacity comparison and Bethe limits.** The pair-marked insertion
  identity gives full endpoint exchange. The countable probability-vector
  inequality then gives equal occupations and equal marginal laws for an
  invariant positive coupling with square-integrable log messages. The
  set of couplings with fixed marginals is weakly compact. A stretched
  upper log tail and a second moment give the integrable edge envelope
  used in the final dominated-convergence step.
  See [ArrivalHardCoupling.lean](Certificate/ArrivalHardCoupling.lean),
  [CavityCouplingCompact.lean](Certificate/CavityCouplingCompact.lean),
  [CavityTightness.lean](Certificate/CavityTightness.lean),
  [BetheEdgeTail.lean](Certificate/BetheEdgeTail.lean), and
  [PressureFormula.lean](Certificate/PressureFormula.lean).

## Remaining links in the manuscript proof

The one-step exposure laws, scaled edge asymptotics and finite-graph
deletion bounds need to be assembled into convergence of the weighted,
fixed-depth neighborhoods and then the finite-graph local-vacancy profile.
The positive-fugacity Bethe derivative calculation still needs its
integrated endpoint exchange on the coupled process. The zero-fugacity
argument still needs uniform two-sided control of the logarithmic tails,
passage from weak convergence of marks to convergence of the recursion,
and existence of an invariant coupling for two candidate laws.
