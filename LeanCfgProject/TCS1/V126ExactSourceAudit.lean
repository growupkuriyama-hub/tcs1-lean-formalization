import LeanCfgProject.TCS1.V88FullManuscriptAudit
import LeanCfgProject.TCS1.V121SubstringReconstruction
import LeanCfgProject.TCS1.V121FiniteInformationClosure
import LeanCfgProject.TCS1.V121TrimAudit
import LeanCfgProject.TCS1.V121LocallyTrivialBridge
import LeanCfgProject.TCS1.V121CappedCounterOne
import LeanCfgProject.TCS1.V121TypedGapKernel
import LeanCfgProject.TCS1.V121TypedGapGrammar
import LeanCfgProject.TCS1.V121SubstringCost
import LeanCfgProject.TCS1.V123TypedFiberEquality
import LeanCfgProject.TCS1.V126LocallyTrivialCore
import LeanCfgProject.TCS1.V126FixedWindowPositiveLocalTrivial
import LeanCfgProject.TCS1.V126NonLocalTrivialWindowObstruction
import LeanCfgProject.TCS1.V126PinFactorizationBridge
import LeanCfgProject.TCS1.V126LinearRegularFilterClosure
import LeanCfgProject.TCS1.V126TypedGapComplete
import LeanCfgProject.TCS1.V126SubstringConstructionCost
import LeanCfgProject.TCS1.V126YieldTypingControl
import LeanCfgProject.TCS1.V126LinearAllFilter
import LeanCfgProject.TCS1.V126DeltaStarCriterion

/-!
# TCS #1 exact-source audit for the v126 re-verification line

The old v88 audit remains the inherited baseline. This file is the
compile-time delta map for theorem-facing changes introduced afterward.

The proof objects live in dedicated modules. These #check commands make this
file fail to compile if a mapped declaration is renamed, removed, or ceases
to elaborate.

External literature inputs are not turned into project axioms. In particular,
Pin's finite-semigroup factorization is represented by the theorem hypothesis
PositiveLengthFactorization in V126PinFactorizationBridge.
-/

namespace LeanCfgProject
namespace TCS1

#check v88_full_manuscript_audited

#check substringBatchLanguage_eq_batchLanguage
#check substring_sample_consistency
#check substring_batchLanguage_sound

#check fixedHSubstitutable_inter_product
#check fixedHSubstitutable_inter_recognized_product
#check fixedHSubstitutable_inverseImage

#check respectsFixedWindowSummary_of_positiveKernelRefinement
#check characteristicPackage_of_positiveWindowKernelRefinement
#check locallyTrivial_between_idempotents
#check locallyTrivial_double_sandwich
#check fixedWindow_positive_image_locally_trivial
#check nonLocalTrivial_obstructs_every_fixedWindow
#check PositiveLengthFactorization
#check positiveWindowKernelRefines_of_factorization
#check locallyTrivial_implies_nn_window_refinement

#check v123_retained_typed_fibre_language_eq

#check v121_factorCandidates_card_le_sq
#check v121_bucket_emissions_le_cube
#check v126_bucket_card_le_sample_card
#check v126_sum_bucket_cards_le_sq
#check v126UnaryPairCount_le_cube
#check v126RuleCandidateCount_le_cubic
#check v126LiteralOutputEnvelope_le_quartic

#check TypedGap.gap_eTop_retained
#check TypedGap.gap_source_has_unit_yield
#check TypedGap.gap_start_language_eq_nonempty
#check TypedGap.gap_source_fixedH
#check TypedGap.gap_source_reduced_package
#check TypedGap.gap_source_shortest_yield_one
#check TypedGap.gap_typed_thickness_at_least_pow_two
#check TypedGap.gap_nonterminal_card
#check TypedGap.gapDisplayedRuleCount_linear
#check TypedGap.gap_semantic_proposition_package

#check rawLinear_fixedH_inter_recognized_product
#check lpmAll_clarkEyraudSubstitutable
#check lpmLanguage_eq_all_inter_parityFilter

#check yieldControl_evalFrom_derives_iff
#check yieldControl_accepts_iff
#check yieldControl_isRegular
#check yieldControlledLanguage_eq_inter

#check CappedCounter.fixedWindowSubstitutable_one

#check DeltaStar.language_iff_balance_zeroHeight_criterion

theorem v126_exact_source_delta_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
