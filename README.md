# Free energy of bipartite random assignment — Lean companion

This repository contains **a partial, machine-checked certificate** for Jacob
Shkrob's [*Free energy of bipartite random assignment*](https://github.com/shkroby/free-energy-assignment/blob/2526291c7b8be51d0993dab0ebd2b13c19015053/main.tex).
The almost-sure free-energy limit, the optional L¹ limit, and existence and
uniqueness of the zero-fugacity cavity law are **not yet proved in Lean**.
[Model.lean](Certificate/Model.lean) states those targets as propositions.
The reduction theorems state their hypotheses explicitly.

The formal target uses the complete square bipartite graph, with a single
infinite array of iid real nonnegative costs, CDF asymptotic
(F(s)\sim \kappa s^d), scale ((\kappa n)^{1/d}), and (d,\beta,\kappa>0).
It represents the lengths in the cavity recursion by scaled rate-one exponential
arrivals. The scope is the main free-energy theorem (`thm:main`). It does not
include the separate quenched overlap theorem added in this manuscript revision.

## Verify

Install [elan](https://leanprover-community.github.io/get_started.html), then run:

```sh
lake exe cache get
bash scripts/check.sh
```

The repository pins Lean 4.33.0 and the matching mathlib release, with exact
transitive revisions in [lake-manifest.json](lake-manifest.json). The check
builds the entire library, looks for unproved declarations and placeholders,
and uses [Audit.lean](Audit.lean) to check transitive kernel axioms for all
exported theorems and to report them for the main results. It accepts only Lean's usual
`propext`, `Classical.choice`, and `Quot.sound`. The audit does not turn an
explicit theorem hypothesis into a proved result.

## Checked results and their limits

| Manuscript argument | Checked Lean result | Remaining input |
|---|---|---|
| Rare short edges | [ShortEdges.lean](Certificate/ShortEdges.lean), [Intensity.lean](Certificate/Intensity.lean): the scaled CDF and scalar binomial-to-Poisson limits; the interval masses and pushforward of the intensity | Joint convergence of marked neighborhoods and identification of the exponential arrivals with the point process |
| Marked Poisson insertion | [PoissonShift.lean](Certificate/PoissonShift.lean): deletion/insertion for a finite Poisson count and independent marks | Identify the full marked arrival process and pass from finite intensity to this process |
| Tree calculation | [Tree.lean](Certificate/Tree.lean), [TreeBoundary.lean](Certificate/TreeBoundary.lean): finite deletion, edge insertion, logarithmic derivative as a sum of monomer marginals, cutoff bound, and nested boundary limits satisfying the crossed recursions. [TreeBipartite.lean](Certificate/TreeBipartite.lean) identifies the tree and completion encodings on finite bipartite graphs. [SoftUniqueness.lean](Certificate/SoftUniqueness.lean) proves extremal equality given the two insertion identities | The insertion identities for those messages on the concrete tree, local limit, finite-graph concentration, and the positive-fugacity Bethe formula |
| Weighted completion | [CompletionPath.lean](Certificate/CompletionPath.lean), [CompletionModel.lean](Certificate/CompletionModel.lean): augmenting path flip, deterministic weighted counting with change and length budgets, and identification of the zero-deficit coefficient with the permanent | Random uniform expansion and row-weight events, and the construction and total budget of the successive paths on those events |
| Removing monomers | [Removal.lean](Certificate/Removal.lean), [Assembly.lean](Certificate/Assembly.lean): the real-exponent uniform pressure gap and the almost-sure transfer by Borel–Cantelli for the actual assignment model | The positive-fugacity limits, convergence of their deterministic values, and the required probabilistic completion estimates |
| Cavity law and simplex inequality | [Simplex.lean](Certificate/Simplex.lean), [Comparison.lean](Certificate/Comparison.lean), [Endpoints.lean](Certificate/Endpoints.lean): the full strict finite/countable simplex inequality, endpoint identities, equality from nonnegative-test endpoint exchange ([ComparisonIntegrability.lean](Certificate/ComparisonIntegrability.lean)), and recovery of identical laws from matching occupations and invariant independent child differences | Uniform log-tail estimates, tightness and passage through the marked series, existence of the invariant coupling, and the marked Poisson exchange on that coupling |
| L¹ convergence | [CompletionCyclic.lean](Certificate/CompletionCyclic.lean): independence of cyclic assignments and the moment-based tail bound; [Integrability.lean](Certificate/Integrability.lean): the L¹ transfer from a uniformly L²-bounded part and a vanishing L¹ error | The estimates deriving the bounded part and vanishing error for the pressure from the row weights and membership in the exceptional events |
| Passing to the pressure formula | [PressureFormula.lean](Certificate/PressureFormula.lean): integrability of the exact exponential intensity envelope, and dominated convergence of the two-term formula | The random-message estimates establishing the envelope and convergence of the expected log messages and edge corrections |

A full certificate would export a theorem of type `Certificate.FreeEnergyClaim`
and pass the same axiom audit on that theorem. This repository does not yet
contain such a theorem.
