import LeanCfgProject.TCS1.IndexedConcreteSSBNFNormalization
import LeanCfgProject.TCS1.SeparatedStartUntypedBridge

/-!
# TCS #1 v69: exact start-language preservation for indexed normalization

The quantitative normalization facade is complemented here by a direct
language theorem.  An original nonterminal is embedded as the corresponding
old state of the finite front-end grammar.  Terminal isolation, binarization,
finite-support restriction, epsilon elimination, unit elimination, productive
and reachable trimming, and finally the fresh separated start are then
connected semantically.

For a source start having at least one nonempty terminal word, the fresh start
generates exactly the source language when its optional epsilon rule is enabled
precisely when the source generates lambda.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedNormalizationLanguage

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/-- Original nonterminal A embedded as an old state of the finite front end. -/
def indexedFiniteFrontEndOldState
    (G : IndexedMixedCFG N α P)
    (A : N) :
    SupportedState
      (indexedNormalizationSupportCertificate G).support :=
  ⟨BinarizedState.old (Sum.inl A), by
    change
      BinarizedState.old (Sum.inl A) ∈
        indexedClosedFrontSupport G
    exact
      indexedClosedFrontSupport_old_mem
        G (Sum.inl A)⟩

/--
The finite front-end restriction preserves the full terminal language of every
original nonterminal exactly.
-/
theorem indexedFiniteFrontEnd_old_language_iff_source
    (G : IndexedMixedCFG N α P)
    (A : N)
    (w : Word α) :
    BinaryNullableDerives
        (indexedFiniteFrontEndGrammar G)
        (indexedFiniteFrontEndOldState G A)
        w
      ↔
    w ∈ LeastClosedLanguage G.toMixedRules A := by
  have hrestrict :=
    restrictedDerives_iff_ambient
      (frontEndBinaryGrammar G.toMixedRules)
      (indexedNormalizationSupportCertificate G).support
      (indexedNormalizationSupportCertificate G).closed
      (indexedFiniteFrontEndOldState G A)
      w
  have hambient :=
    frontEndBinary_derives_iff_interpretation
      G.toMixedRules
      (BinarizedState.old (Sum.inl A))
      w
  change
    BinaryNullableDerives
        (restrictBinaryGrammar
          (frontEndBinaryGrammar G.toMixedRules)
          (indexedNormalizationSupportCertificate G).support)
        (indexedFiniteFrontEndOldState G A)
        w
      ↔
    w ∈ LeastClosedLanguage G.toMixedRules A
  rw [hrestrict]
  simpa [indexedFiniteFrontEndOldState,
    frontEndInterpretation,
    binarizedInterpretation,
    isolatedInterpretation] using hambient

/--
A source nonterminal with one nonempty word gives a productive state after
epsilon and unit elimination.
-/
noncomputable def indexedProductiveUnitFreeState_of_nonempty
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ w : Word α,
        w ∈ LeastClosedLanguage G.toMixedRules A ∧
        w ≠ []) :
    ProductiveUnitFreeState
      (indexedFiniteFrontEndGrammar G) := by
  classical
  let w : Word α := Classical.choose hprod
  have hw :
      w ∈ LeastClosedLanguage G.toMixedRules A :=
    (Classical.choose_spec hprod).1
  have hne : w ≠ [] :=
    (Classical.choose_spec hprod).2
  refine
    ⟨indexedFiniteFrontEndOldState G A, ?_⟩
  have hB :
      BinaryNullableDerives
        (indexedFiniteFrontEndGrammar G)
        (indexedFiniteFrontEndOldState G A)
        w :=
    (indexedFiniteFrontEnd_old_language_iff_source
      G A w).2 hw
  have hE :
      EpsilonFreeDerives
        (indexedFiniteFrontEndGrammar G)
        (indexedFiniteFrontEndOldState G A)
        w :=
    binaryNullableDerives_to_epsilonFree
      (indexedFiniteFrontEndGrammar G) hB hne
  exact
    ⟨w,
      epsilonFreeDerives_to_unitFree
        (indexedFiniteFrontEndGrammar G) hE⟩

/--
Exact source-language theorem for the complete normalized presentation.
The fresh start keeps lambda exactly when the source start generates lambda.
-/
theorem indexedSeparatedStart_language_iff_source
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (w : Word α) :
    BinaryNullableDerives
        (separatedStartGrammar
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod)
          ([] ∈ LeastClosedLanguage G.toMixedRules A))
        none w
      ↔
    w ∈ LeastClosedLanguage G.toMixedRules A := by
  let B :=
    indexedFiniteFrontEndGrammar G
  let start :
      ProductiveUnitFreeState B :=
    indexedProductiveUnitFreeState_of_nonempty
      G A hprod
  have hsep :=
    separatedStart_language_iff_unitFree
      B start
      ([] ∈ LeastClosedLanguage G.toMixedRules A)
      w
  change
    BinaryNullableDerives
        (separatedStartGrammar
          B start
          ([] ∈ LeastClosedLanguage G.toMixedRules A))
        none w
      ↔
    w ∈ LeastClosedLanguage G.toMixedRules A
  rw [hsep]
  constructor
  · intro h
    rcases h with hnil | hunit
    · exact hnil.1 ▸ hnil.2
    · have hE :
          EpsilonFreeDerives B start.1 w :=
        unitFreeDerives_to_epsilonFree B hunit
      have hB :
          BinaryNullableDerives B start.1 w :=
        epsilonFreeDerives_to_binaryNullable B hE
      have hB' :
          BinaryNullableDerives
            (indexedFiniteFrontEndGrammar G)
            (indexedFiniteFrontEndOldState G A)
            w := by
        simpa [B, start,
          indexedProductiveUnitFreeState_of_nonempty] using hB
      exact
        (indexedFiniteFrontEnd_old_language_iff_source
          G A w).1 hB'
  · intro hw
    by_cases hnil : w = []
    · exact Or.inl ⟨hnil, hnil ▸ hw⟩
    · right
      have hB :
          BinaryNullableDerives
            (indexedFiniteFrontEndGrammar G)
            (indexedFiniteFrontEndOldState G A)
            w :=
        (indexedFiniteFrontEnd_old_language_iff_source
          G A w).2 hw
      have hE :
          EpsilonFreeDerives
            (indexedFiniteFrontEndGrammar G)
            (indexedFiniteFrontEndOldState G A)
            w :=
        binaryNullableDerives_to_epsilonFree
          (indexedFiniteFrontEndGrammar G)
          hB hnil
      have hU :
          UnitFreeDerives
            (indexedFiniteFrontEndGrammar G)
            (indexedFiniteFrontEndOldState G A)
            w :=
        epsilonFreeDerives_to_unitFree
          (indexedFiniteFrontEndGrammar G) hE
      simpa [B, start,
        indexedProductiveUnitFreeState_of_nonempty] using hU


/--
The final learner-style start-separated SSBNF presentation has exactly the
original source-start language.  This is the direct semantic bridge from
Appendix A to the hypotheses used by the Section 7 fixed-window learner.
-/
theorem indexedReducedSSBNF_untypedStartLanguage_eq_source
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :
    UntypedStartLanguage
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod))
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod))
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod))
        ([] ∈ LeastClosedLanguage G.toMixedRules A)
      =
    LeastClosedLanguage G.toMixedRules A := by
  apply Set.ext
  intro w
  change
    UntypedStartDerives
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod))
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod))
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod))
        ([] ∈ LeastClosedLanguage G.toMixedRules A)
        w
      ↔
    w ∈ LeastClosedLanguage G.toMixedRules A
  calc
    UntypedStartDerives
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod))
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod))
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod))
        ([] ∈ LeastClosedLanguage G.toMixedRules A)
        w
      ↔
    BinaryNullableDerives
        (separatedStartGrammar
          (indexedFiniteFrontEndGrammar G)
          (indexedProductiveUnitFreeState_of_nonempty
            G A hprod)
          ([] ∈ LeastClosedLanguage G.toMixedRules A))
        none w :=
      reducedSSBNF_untypedStartDerives_iff_separated
        (indexedFiniteFrontEndGrammar G)
        (indexedProductiveUnitFreeState_of_nonempty
          G A hprod)
        ([] ∈ LeastClosedLanguage G.toMixedRules A)
        w
    _ ↔
      w ∈ LeastClosedLanguage G.toMixedRules A :=
      indexedSeparatedStart_language_iff_source
        G A hprod w

end IndexedNormalizationLanguage

end TCS1
end LeanCfgProject
