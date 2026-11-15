import Certificate
import Lean.Util.CollectAxioms

open Lean Elab Command

-- Check declarations directly in the environment; pretty-print wrapping cannot affect the audit.
run_cmd do
  let env ← getEnv
  let candidates := env.constants.fold (init := #[]) fun names name info ↦
    if (`Certificate).isPrefixOf name then
      match info with
      | .thmInfo _ => names.push name
      | _ => names
    else names
  if candidates.isEmpty then
    throwError "The certificate audit found no theorems."
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in candidates do
    let unexpected := (← Lean.collectAxioms name).filter (fun ax ↦ !allowed.contains ax)
    unless unexpected.isEmpty do
      throwError m!"{name} uses unexpected axioms: {unexpected.toList}"
  logInfo m!"Audited {candidates.size} certificate theorems."


#print axioms Certificate.permanent_pos
#print axioms Certificate.measurable_pressure
#print axioms Certificate.tendsto_shortEdge_binomial_mass
#print axioms Certificate.Tree.monomerPartition_vertex_deletion
#print axioms Certificate.Tree.deletionRatio_recursion
#print axioms Certificate.Tree.monomerPartition_zero
#print axioms Certificate.Tree.log_partition_restore_edges_le
#print axioms Certificate.Tree.hasDerivAt_log_monomerPartition_eq_sum_ratios
#print axioms Certificate.TreeBoundary.exists_boundary_limits
#print axioms Certificate.Completion.AugmentingPath.isMatching_flip
#print axioms Certificate.Completion.AugmentingPath.matchedRows_card_flip
#print axioms Certificate.Completion.deficitPartition_zero
#print axioms Certificate.Completion.weightedCompletion_bound_of_real_budget
#print axioms Certificate.Completion.concrete_monomer_pressure_gap
#print axioms Certificate.ae_tendsto_of_monomer_approximation
#print axioms Certificate.simplex_extended_divergence
#print axioms Certificate.simplex_divergence_pos
#print axioms Certificate.occupation_log_ratio
#print axioms Certificate.ae_occupations_eq_of_exchange
#print axioms Certificate.ae_root_log_difference_zero
#print axioms Certificate.map_eq_of_ae_log_difference_zero
#print axioms Certificate.integrable_edge_envelope
#print axioms Certificate.tendsto_bethePressure
#print axioms Certificate.Tree.Bipartite.monomerPartition_eq_grouped
#print axioms Certificate.Tree.Bipartite.monomerPartition_zero_eq_permanent
#print axioms Certificate.SoftUniqueness.ae_eq_of_crossOccupation_identities
#print axioms Certificate.Completion.cyclicCost_independent
#print axioms Certificate.Completion.cyclicCost_min_tail_le
#print axioms Certificate.ae_occupations_eq_of_nonnegative_exchange
#print axioms Certificate.ae_pressure_limit_of_softPressure_and_completion
#print axioms Certificate.intensity_Ioc_zero
#print axioms Certificate.sigmaFinite_intensity
#print axioms Certificate.map_volume_rpow_eq_intensity
#print axioms Certificate.Completion.cyclicCost_min_tail_le_rpow
#print axioms Certificate.tendsto_L1_of_ae_of_L2_add_small_L1
#print axioms Certificate.finite_marked_poisson_insertion
#print axioms Certificate.Completion.pressure_negPart_le_cyclicCost
#print axioms Certificate.Completion.weightedCompletion_certificate
#print axioms Certificate.hard_pressure_exists_of_local_deficit_limits
#print axioms Certificate.pressure_L1_of_ae_limit
#print axioms Certificate.Tree.deletionRatio_between_finiteRootBounds
#print axioms Certificate.ae_tendsto_softAssignmentPressure_of_expected
#print axioms Certificate.canonical_iid_marked_arrival_insertion
#print axioms Certificate.canonical_iid_marked_count_probability
#print axioms Certificate.canonical_marked_window_void
#print axioms Certificate.CanonicalTree.map_root_childPairs
#print axioms Certificate.CanonicalTree.ae_lower_eq_upper
#print axioms Certificate.CanonicalTree.exists_soft_cavity_law
#print axioms Certificate.CanonicalTree.ae_tendsto_cutoff_bounds
#print axioms Certificate.arrival_cavity_median_upperTail
#print axioms Certificate.measure_arrival_weight_tail_gt_le
#print axioms Certificate.hard_pressure_formula_of_local_deficit_limits
#print axioms Certificate.CanonicalTree.existsUnique_soft_cavity_law
#print axioms Certificate.hard_invariant_coupling_marginals_eq
#print axioms Certificate.isCompact_couplingLaws
#print axioms Certificate.LocalExploration.tendsto_canonicalRootCounts_eq
#print axioms Certificate.CanonicalTree.ae_tendsto_cutoff_root
#print axioms Certificate.CanonicalTree.tendsto_expectation_cutoff_root
#print axioms Certificate.hard_cavity_law_marginals_eq_of_invariant
#print axioms Certificate.arrival_log_lowerTail_bound
#print axioms Certificate.integral_softplus_le_of_tail
#print axioms Certificate.isCompact_closure_of_uniform_log_tail
#print axioms Certificate.CanonicalTree.softBethePressure_eq_integral
#print axioms Certificate.CanonicalTree.hard_pressure_formula_of_canonical_cutoff_bethe_limits
#print axioms Certificate.CanonicalTree.exists_hard_cavity_law
#print axioms Certificate.exists_invariant_hard_coupling
#print axioms Certificate.cavityUniquenessClaim
#print axioms Certificate.CanonicalTree.tendsto_bethePressure_softCavityProbability_of_hard_unique
#print axioms Certificate.LocalExploration.adaptiveFreshCosts_conditionalLaw
#print axioms Certificate.LocalExploration.tendsto_oneRootMarkCountEvent_of_null_frontier
#print axioms Certificate.LocalExploration.tendsto_scaled_labelledNeighborhood_mass
#print axioms Certificate.LocalExploration.eventually_integral_short_rootedSimplePathCount_le
#print axioms Certificate.freeEnergyClaim_of_cutoff_bracket_limits
