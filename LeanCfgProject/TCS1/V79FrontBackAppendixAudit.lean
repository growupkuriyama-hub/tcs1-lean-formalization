import LeanCfgProject.TCS1.V79ManuscriptClaimAudit
import LeanCfgProject.TCS1.FixedWindowTreeSurgeryFacade
import LeanCfgProject.TCS1.FixedWindowReducedContextFacade
import LeanCfgProject.TCS1.IndexedNormalizationLanguage
import LeanCfgProject.TCS1.IndexedNormalizationCounts
import LeanCfgProject.TCS1.LinearRawPreprocessingFacade
import LeanCfgProject.TCS1.PreparedLinearNormalizationFacade
import LeanCfgProject.TCS1.ShortestNonemptySpineSemantic
import LeanCfgProject.TCS1.LinearSpineSemantic
import LeanCfgProject.TCS1.LinearSpineBounds
import LeanCfgProject.TCS1.LinearCanonicalWitnessBounds

/-!
# TCS #1 v79: front matter, conclusion, and appendix audit

The numbered-claim audit follows Sections 3--9 theorem by theorem.  This file
covers the remaining theorem-bearing prose of the current v79 manuscript:

* the Abstract and the three contribution bullets in the Introduction;
* the summary claims repeated in the Conclusion; and
* the three appendix proofs supplying the fixed-window and linear
  normalization/witness bounds used by Sections 7 and 8.

Open problems stated in the Conclusion are intentionally not proof
obligations.  Likewise, standard background facts cited from the literature
(such as the deterministic-context-free status of the one-bracket Dyck
language) are not reclassified here as internally proved Lean theorems.

The complexity checks below are the manuscript-level finite
scan/cardinality bounds.  They do not claim a machine-code operational cost
semantics for Lean.
-/

namespace LeanCfgProject
namespace TCS1

-- ---------------------------------------------------------------------------
-- Abstract and Introduction: contribution (1)
-- exact finite-witness reconstruction, conservative Gold learning, and
-- polynomial reconstruction/update work for fixed h.
-- ---------------------------------------------------------------------------

#check indexedFixedH_exists_characteristic_sample
#check exact_reconstruction_of_qualitative_reducedness
#check indexedFixedH_learning_materialized_core
#check materializedConservative_gold_identification_explicit
#check corollary_poly_update_materialized

-- ---------------------------------------------------------------------------
-- Abstract and Introduction: contribution (2)
-- exact fixed-window equivalence, thickness-preserving normalization, and
-- polynomial characteristic data for arbitrary fixed-h linear targets.
-- ---------------------------------------------------------------------------

#check fixedWindowSubstitutable_iff_fixedHSubstitutable
#check fixedWindowSubstitutable_zero_iff_fixedHSubstitutable
#check indexed_proposition74_full_package
#check indexedClassicalFixedWindowSection7_package
#check indexedLinear_normalization_source_package
#check indexedLinear_characteristic_package

-- ---------------------------------------------------------------------------
-- Abstract, Introduction contribution (3), and Conclusion:
-- structural separations and Clark-congruential comparison.
-- ---------------------------------------------------------------------------

#check CappedCounter.regular_fixedH_outside_every_fixedWindow
#check lpm_proposition86_full_semantic
#check DeltaStar.nonlinear_rs_example_full
#check DyckOne.not_fixedH
#check proposition99_fixedH_inclusion
#check proposition99_dyck_properness

-- Section 3 prose used by the introduction's "finite comparison bias"
-- discussion: refinement and product of fixed finite typings.
#check fixedHSubstitutable_of_refinement
#check productFixedFiniteMonoidHom_eq_iff
#check fixedHSubstitutable_product_of_either

-- Section 6 prose used by the Conclusion's limitation discussion:
-- grammar size alone cannot bound positive characteristic-data size.
#check grammarSizeOnlyDataBound_obstruction

-- ---------------------------------------------------------------------------
-- Appendix A.1: proofs of the fixed-window typed-yield and context lemmas.
-- The long-word tree surgery, typed lifting, shortest-path context bound, and
-- common witness envelope are all checked explicitly.
-- ---------------------------------------------------------------------------

#check exists_fixedWindow_cycle_shortened_kernel_ranked
#check exists_fixedWindow_long_typed_yield
#check exists_fixedWindow_bounded_typed_yield
#check fixedWindow_minimal_typed_yield_length_le
#check activeTyped_productive_bounded_yield
#check exists_fixedWindow_reduced_short_reaching_context
#check canonicalYieldContextBounds_fixedWindow_of_structural_reachability
#check canonicalWitnessWords_length_le_fixedWindow_of_structural_reachability

-- ---------------------------------------------------------------------------
-- Appendix A.2: thickness-preserving SSBNF normalization.
-- Language preservation, separated-start form, finite size bounds, and the
-- final Proposition 7.4 package are compile-checked together.
-- ---------------------------------------------------------------------------

#check terminalIsolation_leastClosedLanguage_eq
#check binarization_leastLanguage_eq
#check epsilon_elimination_sameNonemptyLanguage
#check unit_elimination_sameLanguage
#check reducedStart_language_iff_unitFree
#check separatedStart_language_iff_unitFree
#check indexedReducedSSBNF_untypedStartLanguage_eq_source
#check indexedReducedSSBNF_state_card_le_grammarSizeEnvelope
#check indexedReducedSSBNF_terminalRule_card_le_grammarSizeEnvelope
#check indexedReducedSSBNF_binaryRule_card_le_grammarSizeEnvelope
#check indexed_proposition74_full_package

-- ---------------------------------------------------------------------------
-- Appendix B: linear-spine SSBNF normalization.
-- Raw epsilon/unit preprocessing, the concrete prepared normalization,
-- language preservation, one-spine shape, and polynomial size are checked.
-- ---------------------------------------------------------------------------

#check indexedLinear_rawPreprocessedLanguage_eq_source
#check preparedLinear_normalization_package
#check indexedLinear_normalization_source_package
#check indexedLinear_normalization_language_eq
#check indexedLinear_normalization_shape
#check indexedLinear_normalization_size_le
#check indexedLinear_reduced_normalization_semantic_package

-- ---------------------------------------------------------------------------
-- Appendix C: short canonical witnesses for the linear-spine form.
-- Cycle-shortened yield spines, reaching contexts, and final canonical
-- witness-size bounds.
-- ---------------------------------------------------------------------------

#check normalize_linearYieldSpine_to_nodup
#check exists_linear_short_yield
#check linearReachingSpine_short_context
#check linearCanonicalContext_length_le_twice_card
#check mem_canonicalWitnessFinset_linear_length_le
#check canonicalWitnessFinset_linear_norm_le

/--
Compile-time marker: every theorem-bearing claim in the Abstract,
Introduction contribution list, Conclusion summary, and Appendices A--C has
an explicit Lean cross-reference in this audit, except statements explicitly
identified above as literature background or open problems.
-/
theorem v79_front_back_appendix_claims_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
