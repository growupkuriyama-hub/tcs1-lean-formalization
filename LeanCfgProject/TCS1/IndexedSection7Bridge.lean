import LeanCfgProject.TCS1.IndexedNormalizationLanguage
import LeanCfgProject.TCS1.IndexedNormalizationCounts
import LeanCfgProject.TCS1.FixedWindowSection7Package

/-!
# TCS #1: direct indexed-CFG to Section 7 characteristic-data package

This file composes the concrete Appendix-A normalization with the concrete
fixed-window learner.  The source indexed CFG is normalized to the actual
productive/reachable start-separated SSBNF grammar; its non-start symbols have
the verified quadratic thickness bound and its states/rules have the explicit
cubic size bound.  The Section 7 canonical sample can therefore be stated
directly against the original source language.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedSection7Bridge

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/--
The actual final learner non-start grammar inherits the concrete Proposition
7.4 shortest-yield bound.
-/
theorem indexedReducedSSBNF_shortWitness
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
        τR) :
    ∀ X :
      ReducedUnitFreeState
        (indexedFiniteFrontEndGrammar G)
        (indexedProductiveUnitFreeState_of_nonempty
          G A hprod),
      ∃ z : Word α,
        UntypedDerives
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G)
            (indexedProductiveUnitFreeState_of_nonempty
              G A hprod))
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G)
            (indexedProductiveUnitFreeState_of_nonempty
              G A hprod))
          X z
        ∧
        z.length ≤
          ssbnfThicknessEnvelope
            1 1 G.normalizationScale τR := by
  intro X
  obtain ⟨z, hz, hlen⟩ :=
    indexed_proposition74_concreteReducedTrim_thickness
      G τR hn hsource
      (indexedProductiveUnitFreeState_of_nonempty
        G A hprod)
      X
  exact
    ⟨z,
      (reducedSSBNF_untypedDerives_iff
        (indexedFiniteFrontEndGrammar G)
        (indexedProductiveUnitFreeState_of_nonempty
          G A hprod)
        X z).2 hz,
      hlen⟩

/-- Canonical fixed-window sample of the actual indexed normalized grammar. -/
noncomputable def indexedFixedWindowCanonicalSample
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (k l : Nat) :
    Finset (Word α) :=
  @concreteFixedWindowCanonicalSample
    α
    (ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G)
      (indexedProductiveUnitFreeState_of_nonempty
        G A hprod))
    (inferInstance : Fintype α)
    (Fintype.ofFinite _)
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
    k l

/--
End-to-end paper-facing theorem for fixed-h substitutability.

Starting from a finite indexed CFG and its source thickness bound, the actual
normalized SSBNF presentation feeds directly into the concrete h_{k,l}
characteristic-data theorem.  The reconstructed language is the original
source-start language, not merely an abstract normalized presentation.
-/
theorem indexedFixedWindowSection7_package
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR k l : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (LeastClosedLanguage G.toMixedRules A)) :
    BatchLanguage
        (fixedWindowMonoidHom (α := α) k l)
        (indexedFixedWindowCanonicalSample
          G A hprod k l)
      =
    LeastClosedLanguage G.toMixedRules A
    ∧
    (∑ word ∈
      indexedFixedWindowCanonicalSample
        G A hprod k l,
      (word.length + 1))
      ≤
    fixedWindowGrammarSizeEnvelope
      (Fintype.card (FixedWindowMonoid α k l))
      (k + l)
      (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
      (ssbnfThicknessEnvelope
        1 1 G.normalizationScale τR) := by
  classical
  let start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G) :=
    indexedProductiveUnitFreeState_of_nonempty
      G A hprod
  let Nf :=
    ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G) start
  letI : Fintype Nf := Fintype.ofFinite _

  have hlang :
      UntypedStartLanguage
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G) start)
        ([] ∈ LeastClosedLanguage G.toMixedRules A)
        =
      LeastClosedLanguage G.toMixedRules A := by
    simpa [start] using
      indexedReducedSSBNF_untypedStartLanguage_eq_source
        G A hprod

  have hsub' :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (UntypedStartLanguage
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFStartRule
            (indexedFiniteFrontEndGrammar G) start)
          ([] ∈ LeastClosedLanguage G.toMixedRules A)) := by
    rw [hlang]
    exact hsub

  have hshort :
      ∀ X : Nf,
        ∃ z : Word α,
          UntypedDerives
            (reducedSSBNFTerminalRule
              (indexedFiniteFrontEndGrammar G) start)
            (reducedSSBNFBinaryRule
              (indexedFiniteFrontEndGrammar G) start)
            X z
          ∧
          z.length ≤
            ssbnfThicknessEnvelope
              1 1 G.normalizationScale τR := by
    simpa [Nf, start] using
      indexedReducedSSBNF_shortWitness
        G A hprod τR hn hsource

  have hN :
      Fintype.card Nf ≤
        indexedSSBNFGrammarSizeEnvelope
          G.normalizationScale := by
    simpa [Nf] using
      indexedReducedSSBNF_state_card_le_grammarSizeEnvelope
        G start

  have ht :
      (@Fintype.card
        (UntypedTerminalRuleIndex
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
        ≤
      indexedSSBNFGrammarSizeEnvelope
        G.normalizationScale :=
    indexedReducedSSBNF_terminalRule_card_le_grammarSizeEnvelope
      G start

  have hb :
      (@Fintype.card
        (UntypedBinaryRuleIndex
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
        ≤
      indexedSSBNFGrammarSizeEnvelope
        G.normalizationScale :=
    indexedReducedSSBNF_binaryRule_card_le_grammarSizeEnvelope
      G start

  have hpack :=
    concreteFixedWindowSection7_package
      (α := α) (N := Nf)
      (reducedSSBNFTerminalRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFBinaryRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFStartRule
        (indexedFiniteFrontEndGrammar G) start)
      ([] ∈ LeastClosedLanguage G.toMixedRules A)
      k l
      (ssbnfThicknessEnvelope
        1 1 G.normalizationScale τR)
      (indexedSSBNFGrammarSizeEnvelope
        G.normalizationScale)
      (indexedSSBNFGrammarSizeEnvelope
        G.normalizationScale)
      1 1 G.normalizationScale τR
      hsub' hshort hN ht hb
      (le_refl _)
      (le_refl _)

  rw [hlang] at hpack
  simpa [indexedFixedWindowCanonicalSample, Nf, start] using hpack


/-- End-to-end source theorem under classical Yoshinaka (k,l)-substitutability. -/
theorem indexedClassicalFixedWindowSection7_package
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR k l : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hwin :
      FixedWindowSubstitutable
        k l
        (LeastClosedLanguage G.toMixedRules A)) :
    BatchLanguage
        (fixedWindowMonoidHom (α := α) k l)
        (indexedFixedWindowCanonicalSample
          G A hprod k l)
      =
    LeastClosedLanguage G.toMixedRules A
    ∧
    (∑ word ∈
      indexedFixedWindowCanonicalSample
        G A hprod k l,
      (word.length + 1))
      ≤
    fixedWindowGrammarSizeEnvelope
      (Fintype.card (FixedWindowMonoid α k l))
      (k + l)
      (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
      (ssbnfThicknessEnvelope
        1 1 G.normalizationScale τR) := by
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (LeastClosedLanguage G.toMixedRules A) :=
    fixedHSubstitutable_of_fixedWindowSubstitutable
      k l
      (LeastClosedLanguage G.toMixedRules A)
      hwin
  exact
    indexedFixedWindowSection7_package
      G A hprod τR k l hn hsource hsub

/--
The complete indexed-source theorem includes the (0,0) endpoint literally.
Its source-language assumption is ordinary substitutability on nonempty
internal factors.
-/
theorem indexedZeroWindowSection7_package
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
    (hzero :
      NonemptyFactorSubstitutable
        (LeastClosedLanguage G.toMixedRules A)) :
    BatchLanguage
        (fixedWindowMonoidHom (α := α) 0 0)
        (indexedFixedWindowCanonicalSample
          G A hprod 0 0)
      =
    LeastClosedLanguage G.toMixedRules A
    ∧
    (∑ word ∈
      indexedFixedWindowCanonicalSample
        G A hprod 0 0,
      (word.length + 1))
      ≤
    fixedWindowGrammarSizeEnvelope
      (Fintype.card (FixedWindowMonoid α 0 0))
      0
      (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
      (ssbnfThicknessEnvelope
        1 1 G.normalizationScale τR) := by
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) 0 0)
        (LeastClosedLanguage G.toMixedRules A) :=
    (fixedHSubstitutable_zeroWindow_iff_nonemptyFactorSubstitutable
      (α := α)
      (LeastClosedLanguage G.toMixedRules A)).2 hzero
  exact
    indexedFixedWindowSection7_package
      G A hprod τR 0 0 hn hsource hsub

end IndexedSection7Bridge

end TCS1
end LeanCfgProject
