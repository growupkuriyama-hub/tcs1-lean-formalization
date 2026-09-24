import LeanCfgProject.TCS1.RegularRecognition
import LeanCfgProject.TCS1.ClarkEyraudSpecialCase
import LeanCfgProject.TCS1.FixedWindowExactEquivalence
import LeanCfgProject.TCS1.MainTheoremSemanticPackage
import LeanCfgProject.TCS1.MainTheoremExecutablePackage
import LeanCfgProject.TCS1.MainTheoremMaterializedPackage
import LeanCfgProject.TCS1.ConcreteLearnerComplexity
import LeanCfgProject.TCS1.BinaryMembershipDecision
import LeanCfgProject.TCS1.ConservativeMembershipCost
import LeanCfgProject.TCS1.ReconstructionCYKBridge
import LeanCfgProject.TCS1.FiniteUnitReachability
import LeanCfgProject.TCS1.ReconstructionFactorSlotState
import LeanCfgProject.TCS1.ReconstructionFactorSlotCYK
import LeanCfgProject.TCS1.ReconstructionProductionTables
import LeanCfgProject.TCS1.ExecutableConservativeLearner
import LeanCfgProject.TCS1.MaterializedConservativeLearner
import LeanCfgProject.TCS1.MaterializedProductionCost
import LeanCfgProject.TCS1.FixedWindowLemma71ReducedFacade
import LeanCfgProject.TCS1.FixedWindowLemma72Facade
import LeanCfgProject.TCS1.FixedWindowSection7Package
import LeanCfgProject.TCS1.Proposition74IndexedPackage
import LeanCfgProject.TCS1.IndexedLinearNormalizationTheorem
import LeanCfgProject.TCS1.IndexedLinearReducedNormalization
import LeanCfgProject.TCS1.LinearReducedWitnessBridge
import LeanCfgProject.TCS1.IndexedLinearCharacteristicData
import LeanCfgProject.TCS1.LinearSeparatorProposition86
import LeanCfgProject.TCS1.DeltaStarProposition
import LeanCfgProject.TCS1.CappedCounterProposition
import LeanCfgProject.TCS1.FiniteMonoidObstructionKernel
import LeanCfgProject.TCS1.UncappedCounterObstruction
import LeanCfgProject.TCS1.DyckOneBracketKernel
import LeanCfgProject.TCS1.FixedHRightQuotient
import LeanCfgProject.TCS1.ClarkCongruentialComparison

/-!
# TCS #1 v79: theorem-surface audit

This file is a compile-time index from the numbered theorem surface of the
v79 manuscript to the Lean declarations that discharge it.

It indexes theorem-level mathematical verification together with the
representation-level cost bookkeeping needed by the manuscript.  The
repository now includes an
executable CYK kernel for the separated-start SSBNF shape, exact semantic
correctness, explicit polynomial candidate/comparison envelopes, and a bridge
from those envelopes to the concrete conservative learner's positive-data
prefix bounds.  The reconstruction semantics is now presented as an ordinary
finite grammar, its R2/R3 unit rules are eliminated semantically, and the
resulting terminal/binary start language is proved exactly equal to
`BatchLanguage H K`.  The CYK predicate and Boolean wrapper are therefore
connected directly to the actual reconstructed hypothesis.

The representation/decision boundary is now closed at the Lean definition
level.  The reconstruction grammar has been transported to the computable
two-cut factor-slot state space; finite R2/R3 unit reachability is executable;
the specialized CYK Boolean test is no longer `noncomputable`; and the
resulting executable conservative hypothesis sequence is proved pointwise
identical to the semantic Gold run.  The parser-facing terminal, binary, and
start relations are also materialized as explicit finite production tables.
Production-table scanning, unit-closure preprocessing, CYK work, and a
possible rebuild are composed into one explicit prefix-polynomial envelope.

The cost statements are an explicit algorithmic scan/comparison accounting,
not a low-level operational semantics of Lean's evaluator or generated
machine code.

The former external Double-Delta non-linearity fact is no longer external:
the repository now proves its own bounded linear pumping lemma and derives
the obstruction internally.

Every declaration below is checked by the Lean compiler.  Keeping this file in
the full facade makes accidental theorem renaming or loss of a paper-facing
bridge an integration failure.
-/

namespace LeanCfgProject
namespace TCS1

-- Section 3: finite-monoid recognition and classical special cases.
#check regular_auto_proposition_package
#check clarkEyraud_special_case
#check fixedWindowSubstitutable_iff_fixedHSubstitutable
#check fixedWindowSubstitutable_of_fixedHSubstitutable

-- Main qualitative learning theorem and Sections 4--5.
#check sample_consistency
#check batchLanguage_sound
#check typedDerives_yield_type
#check concreteTypedActive_language_eq_untyped
#check canonicalWitnessWords_completeness
#check exact_reconstruction_of_qualitative_reducedness
#check indexedFixedH_exists_characteristic_sample
#check indexedFixedH_learning_semantic_core
#check indexedFixedH_learning_executable_core
#check indexedFixedH_learning_materialized_core
#check indexedFixedH_concreteGold_identification_nonempty

-- Section 6: polynomial reconstruction/update bookkeeping.
#check reconstructionRuleCandidateSpace_card_le_fourth
#check concreteAccumulated_directCandidateScan_le_prefix_degreeFive
#check concreteConservative_update_size_certificate
#check cykStartMember_eq_true_iff
#check cykMembershipCandidateEnvelope_exact
#check cykNaiveComparisonEnvelope_polynomial_form
#check conservativeCYKPrefixEnvelope_polynomial_form
#check concreteConservative_membershipComparison_le_prefix
#check concreteConservative_update_work_le_prefix
#check reconstructionFactorSlot_card_le_outputEncodingEnvelope
#check concreteConservative_occurrenceIndexed_membershipComparison_le_prefix
#check concreteConservative_occurrenceIndexed_update_work_le_prefix
#check reconstructionUnitFree_untypedStartLanguage_eq_batchLanguage
#check reconstructionCYKStartMembership_iff_batchLanguage
#check reconstructionCYKMember_eq_true_iff
#check reconstructionCYK_conservativeComparison_le_prefix
#check finiteUnitReach_eq_true_iff
#check finiteUnitReachScanEnvelope_eq
#check reconstructionFactorSlotNonterminal_observed
#check reconstructionFactorSlotUnitFree_untypedStartLanguage_eq_batchLanguage
#check reconstructionFactorSlotCYKMember_eq_true_iff
#check reconstructionUnitClosureTableScanEnvelope_eq
#check conservativeExecutableUpdateWorkEnvelope_polynomial_form
#check concreteConservative_executable_update_work_le_prefix
#check executableConservativeHypothesis_eq_concrete
#check executableConservative_update_work_le_prefix
#check corollary_poly_update_executable
#check executableConservative_gold_identification_explicit
#check reconstructionFactorSlotUnitFreeTerminalTable_card_le
#check reconstructionFactorSlotUnitFreeBinaryTable_card_le
#check reconstructionFactorSlotUnitTable_card_le
#check reconstructionMaterializedCYKMember_eq_true_iff
#check materializedConservativeUpdate_eq_executable
#check materializedConservativeHypothesis_eq_concrete
#check materializedConservative_gold_identification_explicit
#check reconstructionProductionTableScanEnvelope_polynomial_form
#check reconstructionMaterializedProductionCard_le_scanEnvelope
#check concreteConservative_materializedProductionCard_le_prefix
#check materializedConservative_productionCard_le_prefix
#check conservativeMaterializedUpdateWorkEnvelope_polynomial_form
#check concreteConservative_materialized_update_work_le_prefix
#check materializedConservative_update_work_le_prefix
#check corollary_poly_update_materialized

-- Section 7: fixed-window quantitative bounds and normalization transfer.
#check omittedSibling_contribution_le
#check boundaryAssembly_typed_lift_of_fixedWindowSummary
#check terminalIsolation_then_binarization_language_eq
#check frontEndBinary_active_short_derivation_envelope
#check fixedWindow_reduced_minimal_typed_yield_length_le
#check canonicalWitnessWords_length_le_fixedWindow
#check concreteFixedWindowSection7_package
#check classicalFixedWindowSection7_package
#check indexedClassicalFixedWindowSection7_package
#check indexedZeroWindowSection7_package
#check indexed_proposition74_full_package
#check proposition74_thickness_from_yieldBound

-- Section 8: arbitrary linear normalization, short witnesses, and data bound.
#check indexedLinear_normalization_source_package
#check indexedLinear_reduced_normalization_semantic_package
#check minimumCanonicalYield_linear_length_le
#check minimumCanonicalContext_linear_length_le
#check indexedLinear_characteristic_package
#check lpm_proposition86_full_semantic

-- Section 9.1: nonlinear Delta-star example.
#check DeltaStar.nonlinear_rs_example_verified_core
#check DeltaStar.doubleDelta_not_rawLinearInitialRepresentable
#check DeltaStar.deltaStar_not_rawLinearRepresentable
#check DeltaStar.deltaStar_no_indexedLinear_presentation
#check DeltaStar.nonlinear_rs_example_nonlinearity_reduction
#check DeltaStar.nonlinear_rs_example_full

-- Section 9.2: regular separation from all fixed windows.
#check CappedCounter.proposition_ctr_regular
#check CappedCounter.theorem_ctr_non_kl
#check CappedCounter.regular_fixedH_outside_every_fixedWindow

-- Section 9.3: finite-monoid obstructions and quotient closure.
#check finiteMonoid_obstruction
#check finiteMonoid_obstruction_uniform
#check UncappedCounter.not_fixedH
#check DyckOne.not_fixedH
#check fixedHSubstitutable_fixedRightQuotient

-- Proposition 9.9: comparison with Clark's congruential family.
#check proposition99_fixedH_inclusion
#check proposition99_dyck_properness

/-- Marker theorem: the current v79 theorem-surface audit compiles. -/
theorem v79_theorem_surface_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
