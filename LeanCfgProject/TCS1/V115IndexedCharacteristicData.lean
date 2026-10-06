import LeanCfgProject.TCS1.V115IndexedNormalizationYieldBridge
import LeanCfgProject.TCS1.IndexedNormalizationCounts

/-!
# TCS #1 v115: characteristic-data norm from an indexed source CFG

This file composes the two independently verified components used
in the revised Corollary 7.5:

* Proposition 7.4 provides the concrete reduced-SSBNF grammar and
  a short productive yield bounded in terms of the indexed *source*
  grammar's normalization scale and ordinary thickness.
* The locally-trivial positive-image theorem gives an exact
  norm bound for the h-typed canonical characteristic witness set
  from those productive yields.

The resulting bound is a fixed polynomial in the finite source
grammar's normalization scale and the source ordinary thickness.
The assumptions on h and the existence of a nonempty successful
start derivation remain explicit; no axiom or placeholder proof is
introduced.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w x

section V115IndexedCharacteristicData

variable {N : Type u} {α : Type v} {P : Type w}
variable {M : Type x} [Monoid M] [Fintype M]
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α] [Nonempty α]

/--
An explicit polynomial norm bound for the *actual* canonical
characteristic witness finset of the h-typed normalization of
a finite indexed source CFG.

For a fixed homomorphism h, put n=|h(Sigma+)| and m=|M|.
The result is polynomial in the normalization scale s of the
source CFG and its ordinary thickness tau_R.  The coarse size
envelope s+s^2+s^3 bounds all three normalized counts.
-/
theorem v115_indexedLocallyTrivial_canonicalSampleNorm
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (G : IndexedMixedCFG N α P)
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage G.toMixedRules A)
        τR)
    (start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G))
    (keepEmpty : Prop)
    (C :
      ReducedWitnessChoices
        H
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G) start)
        keepEmpty
        (ConcreteTypedActive H
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFStartRule
            (indexedFiniteFrontEndGrammar G) start)))
    (minimal :
      CanonicalChoiceMinimality
        H
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G) start)
        keepEmpty
        (ConcreteTypedActive H
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFStartRule
            (indexedFiniteFrontEndGrammar G) start))
        C) :
    (∑ w ∈
      canonicalWitnessFinset
        H
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G) start)
        keepEmpty
        (ConcreteTypedActive H
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFStartRule
            (indexedFiniteFrontEndGrammar G) start))
        C,
      (w.length + 1)) ≤
    typedThicknessWitnessCountEnvelope
      (Fintype.card M)
      (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
      (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
      (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
      *
      (((indexedSSBNFGrammarSizeEnvelope G.normalizationScale
            * Fintype.card M + 1) *
          fixedWindowTypedYieldBound
            (v115PositiveImageCard H + v115PositiveImageCard H)
            (indexedSSBNFGrammarSizeEnvelope G.normalizationScale)
            (ssbnfThicknessEnvelope 1 1 G.normalizationScale τR))
        + 1) := by
  classical
  let B := indexedFiniteFrontEndGrammar G
  let NT := ReducedUnitFreeState B start
  let t := reducedSSBNFTerminalRule B start
  let b := reducedSSBNFBinaryRule B start
  let s := reducedSSBNFStartRule B start
  let Active := ConcreteTypedActive H t b s
  letI : Fintype NT := Fintype.ofFinite _
  letI : Fintype (ActiveTypedSymbol Active) := Fintype.ofFinite _
  letI : Fintype (ActiveTypedTerminalIndex H t Active) := Fintype.ofFinite _
  letI : Fintype (ActiveTypedBinaryIndex b Active) := Fintype.ofFinite _
  letI : Fintype (UntypedTerminalRuleIndex t) := Fintype.ofFinite _
  letI : Fintype (UntypedBinaryRuleIndex b) := Fintype.ofFinite _
  let S := indexedSSBNFGrammarSizeEnvelope G.normalizationScale
  let m := Fintype.card M
  let τ := ssbnfThicknessEnvelope 1 1 G.normalizationScale τR
  let r := v115PositiveImageCard H + v115PositiveImageCard H
  let Bshort := fixedWindowTypedYieldBound r (Fintype.card NT) τ
  have hshort :
      ∀ A : NT,
        ∃ z : Word α,
          UntypedDerives t b A z ∧ z.length ≤ τ :=
    v115_indexedNormalization_untypedYieldBound G τR hn hsource start
  have hnorm :
      (∑ w ∈ canonicalWitnessFinset H t b s keepEmpty Active C,
         (w.length + 1))
        ≤
      typedThicknessWitnessCountEnvelope
        m (Fintype.card NT)
        (Fintype.card (UntypedTerminalRuleIndex t))
        (Fintype.card (UntypedBinaryRuleIndex b))
        *
      (((Fintype.card NT * m + 1) * Bshort) + 1) :=
    v115_locallyTrivial_sampleNorm_le_ordinaryThickness
      H t b s keepEmpty C minimal hlocal τ hshort
  have hNT : Fintype.card NT ≤ S :=
    indexedReducedSSBNF_state_card_le_grammarSizeEnvelope G start
  have ht : Fintype.card (UntypedTerminalRuleIndex t) ≤ S :=
    indexedReducedSSBNF_terminalRule_card_le_grammarSizeEnvelope G start
  have hb : Fintype.card (UntypedBinaryRuleIndex b) ≤ S :=
    indexedReducedSSBNF_binaryRule_card_le_grammarSizeEnvelope G start
  have hcount :
      typedThicknessWitnessCountEnvelope m
        (Fintype.card NT)
        (Fintype.card (UntypedTerminalRuleIndex t))
        (Fintype.card (UntypedBinaryRuleIndex b))
      ≤ typedThicknessWitnessCountEnvelope m S S S := by
    have hfirst := Nat.mul_le_mul_right m hNT
    have hlast := Nat.mul_le_mul_right (m ^ 2) hb
    unfold typedThicknessWitnessCountEnvelope
    omega
  have hB :
      Bshort ≤ fixedWindowTypedYieldBound r S τ :=
    fixedWindowTypedYieldBound_mono_N hNT
  have hword :
      (((Fintype.card NT * m + 1) * Bshort) + 1) ≤
      (((S * m + 1) *
          fixedWindowTypedYieldBound r S τ) + 1) := by
    have hfactor :
        Fintype.card NT * m + 1 ≤ S * m + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right m hNT) 1
    exact Nat.add_le_add_right (Nat.mul_le_mul hfactor hB) 1
  have hproduct := Nat.mul_le_mul hcount hword
  exact hnorm.trans (by simpa only [B, NT, t, b, s, Active,
       m, τ, r, S, Bshort] using hproduct)

end V115IndexedCharacteristicData
end TCS1
end LeanCfgProject
