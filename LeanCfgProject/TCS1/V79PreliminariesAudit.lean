import LeanCfgProject.TCS1.FixedHomEvaluation
import LeanCfgProject.TCS1.GeneralCFGDerivation
import LeanCfgProject.TCS1.LeastClosedCFGLanguage
import LeanCfgProject.TCS1.ReconstructionComplexityCounts
import LeanCfgProject.TCS1.ConcreteConservativeLearner
import LeanCfgProject.TCS1.TrivialTargetEndpoints

/-!
# TCS #1 v79: preliminaries and learning-model audit

This file covers the theorem-bearing statements in Section 2 that are not
numbered propositions later in the paper.

Most of Section 2 is definitional setup.  The compile-time checks below record
the concrete Lean objects used for distributions, CFG semantics, positive-data
sample size, conservative updates, and the empty/epsilon endpoints.

The fixed homomorphism computation claim is strengthened by
`fixedHom_linear_scan_certificate`: with the multiplication table and letter
images treated as fixed data, the evaluator performs exactly one monoid
multiplication per input symbol.

The manuscript's convention that reasonable CFG encodings are polynomially
equivalent is a representation convention, not a formal theorem about a
specific byte encoding, and is therefore not asserted here.
-/

namespace LeanCfgProject
namespace TCS1

-- Terminal contexts and distributions.
#check Distribution
#check HaveSharedContext
#check sharedContext_iff_distribution_inter_nonempty

-- General CFG derivation semantics used by normalization and target proofs.
#check MixedDerives
#check MixedSymbolsDerive
#check MixedNonterminalLanguage
#check LeastClosedLanguage

-- Fixed finite-monoid typing and the Section 2 linear-scan evaluation claim.
#check FixedFiniteMonoidHom
#check FixedHSubstitutable
#check fixedHomLetterProduct_eq_h
#check fixedHomMultiplicationCount_eq_length
#check fixedHom_linear_scan_certificate

-- Positive-data sample measure.  In particular, the number of examples is
-- bounded by the same norm used in the polynomial statements.
#check reconstructionSampleNorm
#check reconstructionSample_card_le_norm

-- Set-driven reconstruction and the concrete conservative sequential update.
#check BatchLanguage
#check sample_consistency
#check concreteAccumulatedSample
#check concreteConservativeHypothesis_keep
#check concreteConservativeHypothesis_rebuild

-- Empty and epsilon-only target conventions from the learning-model setup.
#check batchLanguage_empty_eq
#check batchLanguage_singleton_epsilon_eq
#check singletonEpsilon_fixedHSubstitutable
#check singletonEpsilon_concreteGold_identification

/--
Compile-time marker for the theorem-bearing claims and conventions of the
Preliminaries section that are represented internally in the Lean
development.
-/
theorem v79_preliminaries_claims_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
