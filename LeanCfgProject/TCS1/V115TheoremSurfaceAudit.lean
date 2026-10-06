import LeanCfgProject.TCS1.V88FullManuscriptAudit
import LeanCfgProject.TCS1.V79ManuscriptClaimAudit
import LeanCfgProject.TCS1.V115FiniteInformationClosure
import LeanCfgProject.TCS1.V115InverseHomClosure
import LeanCfgProject.TCS1.V115PositiveImageCardinal
import LeanCfgProject.TCS1.V115LocalConsequences
import LeanCfgProject.TCS1.V115IndexedCharacteristicPackage
import LeanCfgProject.TCS1.V115DeltaStarDPDA

/-!
# TCS #1 v115: exact 30-claim crosswalk (not yet a full-proof certificate)

Source: `Papers/01_fixed-h-cfg/main.tex`, internal v115,
the 30 theorem/proposition/lemma/corollary environments in source order.
The source has 30 numbered claim environments.

The checks below name the existing verified declarations against each
manuscript claim. A `#check` does not establish exact equivalence
with the whole English-language proposition: it only resolves and
type-checks an already defined Lean statement.

Explicit remaining gaps:
* Proposition 3.2: language-family CFL closure under regular
  intersection and arbitrary erasing inverse homomorphism.
  The RS_h semantic substitutability portions ARE formalized.
* Theorem 3.4: verify the exact complete conjunction of all
  assertions, including uniform running-time details in the v115 wording.
* Proposition 9.1: DPDA recognizer must be integrated with the
  previous nonlinear/finite-typing evidence, without weakening
  the manuscript's deterministic-CFL interpretation.
* Source-v115-specific assertions and unnumbered claims not
  individually covered by these checks require separate review.

No vacuous `True`-valued theorem here claims all v115 proof
obligations discharged.
-/

namespace LeanCfgProject
namespace TCS1

--  1 / prop:regular-auto
#check regular_auto_proposition_package

--  2 / prop:finite-info-closure
-- (i): semantic intersections; (ii): recognized filtering of RS;
-- (iii): erasing inverse image of RS_h.
-- CFL representation-level variants of (ii) and (iii) are OPEN.
#check fixedHSubstitutable_inter_product
#check fixedHSubstitutable_inter_recognized_product
#check fixedHSubstitutable_substitutionPreimage

--  3 / prop:yl-special
#check fixedWindowSubstitutable_iff_fixedHSubstitutable

--  4 / thm:main (several distinct clauses; final conjunction OPEN)
#check indexedFixedH_learning_materialized_core
#check corollary_poly_update_materialized
#check indexedClassicalFixedWindowSection7_package
#check indexedLinear_characteristic_package
#check v115_indexedLocallyTrivial_characteristic_package

--  5 / prop:li-window (fixed-window / positive semigroup)
#check v115_positiveImageLocallyTrivial_of_fixedWindow_refinement
#check v115_positiveImageLocallyTrivial_window_refines
#check v115_locallyTrivial_length_card_idempotent
#check v115_fixedWindow_positiveImageLocallyTrivial
#check v115_localSubstitutable_is_fixedWindowSubstitutable

--  6 / lem:sample-consistency
#check sample_consistency

--  7 / thm:soundness
#check batchLanguage_sound

--  8 / prop:typed-core
#check concreteTypedActive_language_eq_untyped
#check typedDerives_yield_type

--  9 / thm:complete
#check canonicalWitnessWords_completeness

-- 10 / thm:reconstruction-fixed-h
#check exact_reconstruction_of_qualitative_reducedness

-- 11 / cor:ilt
#check indexedFixedH_concreteGold_identification_nonempty
#check materializedConservative_gold_identification_explicit

-- 12 / thm:poly-build
#check reconstructionOutputEncodingEnvelope_le_degreeFive
#check concreteAccumulated_directCandidateScan_le_prefix_degreeFive

-- 13 / lem:typed-thickness-bound
#check canonicalContext_length_le_of_typedYieldBound
#check canonicalWitnessWords_length_le_typedThickness
#check canonicalWitnessFinset_sampleNorm_le_typedThickness

-- 14 / cor:typed-thickness-data
#check canonicalWitnessFinset_sampleNorm_le_typedThickness
#check concreteTypedActive_language_eq_untyped

-- 15 / lem:window-typed-yield
#check fixedWindow_reduced_minimal_typed_yield_length_le

-- 16 / thm:window-thick
#check concreteFixedWindowSection7_package
#check classicalFixedWindowSection7_package

-- 17 / prop:thick-ssbnf-normal
#check indexed_proposition74_full_package
#check indexedReducedSSBNF_untypedStartLanguage_eq_source

-- 18 / cor:window-transfer
#check indexedFixedWindowSection7_package
#check indexedClassicalFixedWindowSection7_package

-- 19 / cor:li-thickness (new to v115)
#check v115_indexedLocallyTrivial_characteristic_package
#check v115_indexedLocallyTrivial_canonicalSampleNorm

-- 20 / prop:linear-normal
#check indexedLinear_normalization_source_package

-- 21 / lem:linear-short
#check minimumCanonicalYield_linear_length_le

-- 22 / thm:linear-poly
#check indexedLinear_characteristic_package

-- 23 / prop:linear-separator-example
#check lpm_proposition86_full_semantic

-- 24 / prop:nonlinear-rs-example
#check DeltaStar.nonlinear_rs_example_full
#check DeltaStar.deltaStar_deterministic_pushdown

-- 25 / thm:ctr-non-kl
#check CappedCounter.theorem_ctr_non_kl

-- 26 / lem:finite-monoid-obstruction
#check finiteMonoid_obstruction

-- 27 / anonymous corollary: CTR outside RS
#check UncappedCounter.not_fixedH

-- 28 / cor:dyck-not-rs
#check DyckOne.not_fixedH

-- 29 / lem:rs-fixed-quotient
#check fixedHSubstitutable_fixedRightQuotient

-- 30 / prop:clark-congruential-comparison
#check proposition99_fixedH_inclusion
#check proposition99_dyck_properness

end TCS1
end LeanCfgProject
