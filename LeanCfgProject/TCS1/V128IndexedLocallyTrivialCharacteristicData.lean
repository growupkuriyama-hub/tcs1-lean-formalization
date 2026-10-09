import LeanCfgProject.TCS1.IndexedFixedHBridge
import LeanCfgProject.TCS1.IndexedSection7Bridge
import LeanCfgProject.TCS1.V128IndexedNormalizationCertificate
import LeanCfgProject.TCS1.V128LocallyTrivialThickness

/-!
# TCS #1 v128: indexed-source locally trivial characteristic data

This is the source-level composition of the fixed-h canonical sample
(the *original* typing H), the indexed SSBNF construction, its polynomial
witness/grammar-count bounds, and positive-image local triviality.

Unlike the abstract `V128LocallyTrivialThickness` interface, the source
normalization hypotheses `hshort`, `hN`, `ht`, `hb`, `hg` and `hτ`
are all discharged here from concrete existing normalization theorems.

This theorem covers sources with a nonempty *positive* terminal word and an
explicit source nonterminal yield bound. The epsilon-only target and the
identification of source encoding parameters with the paper's arbitrary
reduced-CFG size/thickness conventions are separate obligations.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section V128IndexedLocallyTrivialCharacteristicData

variable {N : Type u} {α : Type v} {P : Type w}
variable {M : Type q} [Monoid M] [Fintype M]
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/-- Concrete source-indexed characteristic data for a locally trivial
positive-image homomorphism. The reconstruction uses the *original* H,
not the larger fixed-window type. The norm is bounded by a polynomial
expression in the source encoding scale and its yield bound. -/
theorem indexedLocallyTrivialCharacteristicData_package
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    BatchLanguage H
        (indexedFixedHCanonicalSample H G A hprod)
      =
      LeastClosedLanguage G.toMixedRules A
    ∧
    (∑ word ∈ indexedFixedHCanonicalSample H G A hprod,
      (word.length + 1)) ≤
      fixedWindowGrammarSizeEnvelope
        (Fintype.card M)
        (positiveWindowBound H + positiveWindowBound H)
        (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
        (ssbnfThicknessEnvelope 1 1 G.normalizationScale τR) := by
  classical
  let start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G) :=
    indexedProductiveUnitFreeState_of_nonempty G A hprod
  let Nf :=
    ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G) start
  letI : Fintype Nf := Fintype.ofFinite _

  have hshort :
      ∀ X : Nf,
        ∃ z : Word α,
          UntypedDerives
            (reducedSSBNFTerminalRule
              (indexedFiniteFrontEndGrammar G) start)
            (reducedSSBNFBinaryRule
              (indexedFiniteFrontEndGrammar G) start)
            X z
          ∧ z.length ≤
              ssbnfThicknessEnvelope
                1 1 G.normalizationScale τR := by
    simpa [Nf, start] using
      indexedReducedSSBNF_shortWitness
        G A hprod τR hn hsource

  have hN :
      Fintype.card Nf ≤
        indexedSSBNFGrammarSizeEnvelope G.normalizationScale := by
    simpa [Nf] using
      indexedReducedSSBNF_state_card_le_grammarSizeEnvelope G start

  have ht :
      (@Fintype.card
        (UntypedTerminalRuleIndex
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
        ≤ indexedSSBNFGrammarSizeEnvelope G.normalizationScale :=
    indexedReducedSSBNF_terminalRule_card_le_grammarSizeEnvelope G start

  have hb :
      (@Fintype.card
        (UntypedBinaryRuleIndex
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
        ≤ indexedSSBNFGrammarSizeEnvelope G.normalizationScale :=
    indexedReducedSSBNF_binaryRule_card_le_grammarSizeEnvelope G start

  constructor
  · exact indexedFixedHCanonicalSample_characteristic
      H G A hprod hsub
  · have hnorm :=
      locallyTrivialMinimalCanonicalSample_norm_le_ssbnf
        H
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G) start)
        ([] ∈ LeastClosedLanguage G.toMixedRules A)
        hlocal
        (ssbnfThicknessEnvelope 1 1 G.normalizationScale τR)
        (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
        (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
        1 1 G.normalizationScale τR
        hshort hN ht hb (le_refl _) (le_refl _)
    simpa [indexedFixedHCanonicalSample, Nf, start] using hnorm

end V128IndexedLocallyTrivialCharacteristicData

end TCS1
end LeanCfgProject
