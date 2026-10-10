import LeanCfgProject.TCS1.V79ManuscriptClaimAudit
import LeanCfgProject.TCS1.V88FullManuscriptAudit
import LeanCfgProject.TCS1.V83TypedThicknessWitnessBounds
import LeanCfgProject.TCS1.V128RetainedTypedLanguageEquality
import LeanCfgProject.TCS1.V128SubstringEffectiveBinaryTable
import LeanCfgProject.TCS1.V128ThicknessGapClassMembership
import LeanCfgProject.TCS1.V128ErasureFlagTyping
import LeanCfgProject.TCS1.V128TypedTrimSuccessfulBranch

/-!
# TCS #1 v128: 30 numbered-claim crosswalk (not a completion certificate)

This file typechecks concrete mathematical declarations mapped, one by one,
to the thirty numbered theorem/proposition/lemma/corollary environments in
Papers/01_fixed-h-cfg/main.tex, internal manuscript version v128.

The exact logical correspondence and remaining gaps are recorded in
V128_NUMBERED_CLAIMS_ONE_TO_ONE_AUDIT_2026-10-09.md.

Crucially: these #checks verify existing declaration names/types, NOT
a newly claimed complete v128 proof. Open claims are marked explicitly,
and no tautological True marker is introduced to hide an obligation.
-/

namespace LeanCfgProject
namespace TCS1

-- 01 prop:regular-auto (reuse)
#check regular_auto_proposition_package
#check regular_exists_fixedHSubstitutable

-- 02 prop:finite-info-closure (partial; CFL closure parts external)
#check fixedHSubstitutable_inter_product
#check fixedHSubstitutable_regularFilter_product
#check inverseImage_fixedHSubstitutable_with_erasureFlag

-- 03 prop:yl-special (reuse)
#check fixedWindowSubstitutable_iff_fixedHSubstitutable

-- 04 thm:main (bridge; item (iv) depends on 05 and 19)
#check indexedFixedH_learning_materialized_core
#check corollary_poly_update_materialized
#check indexedClassicalFixedWindowSection7_package
#check indexedLinear_characteristic_package

-- 05 prop:li-window (OPEN: positive-image locally trivial iff
-- finite-window kernel refinement, n = |image(Sigma+)|+1).
-- No complete Lean theorem is asserted here.
#check fixedWindowSubstitutable_iff_fixedHSubstitutable
#check fixedHSubstitutable_of_refinement

-- 06 lem:sample-consistency
#check sample_consistency

-- 07 thm:soundness
#check batchLanguage_sound
#check substringBatchLanguage_eq_batchLanguage

-- 08 prop:typed-core (retained typed fibers)
#check concreteTypedActive_language_eq_untyped
#check typedDerives_yield_type
#check retainedTypedNonstartLanguage_eq_inter_fiber

-- 09 thm:complete
#check canonicalWitnessWords_completeness
#check substringBatchLanguage_eq_batchLanguage

-- 10 thm:reconstruction-fixed-h
#check exact_reconstruction_of_qualitative_reducedness
#check v116TabulatedBatchLanguage_eq_batchLanguage

-- 11 cor:ilt (bridge for v116 concrete sequential hypotheses)
#check indexedFixedH_concreteGold_identification_nonempty
#check materializedConservative_gold_identification_explicit

-- 12 thm:poly-build (existing polynomial envelope;
-- v116 quartic accounting not yet complete).
#check reconstructionRuleCandidateSpace_card_le_fourth
#check reconstructionOutputEncodingEnvelope_le_degreeFive
#check materializedConservative_update_work_le_prefix
#check substringBucketKeys_unaryCandidateCount_le_cube
#check v116BinaryRuleTable_card_le_cube
#check v116EffectiveBinaryWordTable_eq_actual
#check substringV116DirectOutputBudget_le_quartic

-- 13 lem:typed-thickness-bound
#check reachingSpine_context_length_le_card_sub_one
#check canonicalWitnessWords_length_le_typedThickness
#check canonicalWitnessFinset_sampleNorm_le_typedThickness

-- 14 cor:typed-thickness-data
#check canonicalWitnessFinset_sampleNorm_le_typedThickness
#check indexedFixedH_exists_characteristic_sample

-- 15 prop:typed-thickness-gap
#check v128_exponential_gap_manuscript_instance
#check v128_exponential_gap_explicit_bounds

-- 16 lem:window-typed-yield
#check fixedWindow_reduced_minimal_typed_yield_length_le

-- 17 thm:window-thick
#check concreteFixedWindowSection7_package
#check classicalFixedWindowSection7_package

-- 18 prop:thick-ssbnf-normal
#check indexed_proposition74_full_package
#check proposition74_thickness_from_yieldBound

-- 19 cor:li-thickness (OPEN: depends on the missing 05 criterion;
-- these are only partial component declarations).
#check retainedTypedNonstartLanguage_eq_inter_fiber
#check typedStartBinary_children_derivations_survive_trim
#check fixedWindow_reduced_minimal_typed_yield_length_le
#check indexed_proposition74_full_package

-- 20 prop:linear-normal
#check indexedLinear_normalization_source_package
#check indexedLinear_normalization_language_eq
#check indexedLinear_normalization_shape
#check indexedLinear_normalization_size_le

-- 21 lem:linear-short
#check minimumCanonicalYield_linear_length_le
#check minimumCanonicalContext_linear_length_le

-- 22 thm:linear-poly
#check indexedLinear_characteristic_package

-- 23 prop:linear-separator-example
#check lpm_proposition86_full_semantic

-- 24 prop:nonlinear-rs-example
#check DeltaStar.nonlinear_rs_example_full
#check DeltaStar.deltaStar_no_indexedLinear_presentation

-- 25 thm:ctr-non-kl
#check CappedCounter.theorem_ctr_non_kl

-- 26 lem:finite-monoid-obstruction
#check finiteMonoid_obstruction
#check finiteMonoid_obstruction_uniform

-- 27 unlabeled corollary at v128 TeX line 1636 (CTR not in RS)
#check UncappedCounter.not_fixedH

-- 28 cor:dyck-not-rs
#check DyckOne.not_fixedH

-- 29 lem:rs-fixed-quotient
#check fixedHSubstitutable_fixedRightQuotient

-- 30 prop:clark-congruential-comparison
#check proposition99_fixedH_inclusion
#check proposition99_dyck_properness

end TCS1
end LeanCfgProject
