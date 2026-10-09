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
  -- Keep the finite rule-index instances coherent with the concrete
  -- normalization-count bounds (which use Fintype.ofFinite).
  letI : Fintype
      (UntypedTerminalRuleIndex
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start)) :=
    Fintype.ofFinite _
  letI : Fintype
      (UntypedBinaryRuleIndex
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start)) :=
    Fintype.ofFinite _

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

/--
Source-level characteristic data for **every nonempty** indexed target under
the locally trivial positive-image hypothesis. In the positive-word case it
reuses the concrete indexed normalization theorem. If the target has no
nonempty word, nonemptiness forces the language to be exactly `{[]}`, and
the existing epsilon-only characteristic sample is used.

The additional constant `1` makes the same displayed polynomial envelope
valid also for the epsilon-only endpoint. Source yield and normalization
hypotheses are still explicit; this is not yet an exact arbitrary-reduced-CFG
formulation of manuscript `cor:li-thickness`.
-/
theorem indexedLocallyTrivialCharacteristicData_nonempty_package
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hnonempty :
      ∃ w : Word α, w ∈ LeastClosedLanguage G.toMixedRules A)
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    ∃ K : Finset (Word α),
      BatchLanguage H K =
        LeastClosedLanguage G.toMixedRules A
      ∧
      (∑ word ∈ K, (word.length + 1)) ≤
        1 + fixedWindowGrammarSizeEnvelope
          (Fintype.card M)
          (positiveWindowBound H + positiveWindowBound H)
          (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
          (ssbnfThicknessEnvelope 1 1 G.normalizationScale τR) := by
  classical
  by_cases hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧ u ≠ []
  · obtain ⟨hchar, hnorm⟩ :=
      indexedLocallyTrivialCharacteristicData_package
        H hlocal G A hprod τR hn hsource hsub
    refine ⟨indexedFixedHCanonicalSample H G A hprod, hchar, ?_⟩
    omega
  · have hL :
        LeastClosedLanguage G.toMixedRules A =
          ({[]} : Set (Word α)) := by
      apply Set.ext
      intro w
      constructor
      · intro hw
        have hw0 : w = [] := by
          by_contra hne
          exact hprod ⟨w, hw, hne⟩
        simpa [hw0]
      · intro hw
        have hw0 : w = [] := by
          simpa using hw
        subst w
        obtain ⟨z, hz⟩ := hnonempty
        have hz0 : z = [] := by
          by_contra hzne
          exact hprod ⟨z, hz, hzne⟩
        simpa [hz0] using hz
    refine ⟨({[]} : Finset (Word α)), ?_, ?_⟩
    · simpa [hL] using singletonEpsilon_characteristic H
    · simp

end V128IndexedLocallyTrivialCharacteristicData

end TCS1
end LeanCfgProject
