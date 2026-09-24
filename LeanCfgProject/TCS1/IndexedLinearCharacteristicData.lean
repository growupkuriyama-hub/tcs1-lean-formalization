import LeanCfgProject.TCS1.IndexedLinearNormalizationTheorem
import LeanCfgProject.TCS1.ConcreteLinearCharacteristicData
import LeanCfgProject.TCS1.LinearCharacteristicSourceBounds

/-!
# TCS #1 v79: characteristic data for arbitrary finite indexed linear CFGs

This module closes the paper-facing bridge for Theorem 8.3 (polynomial
characteristic data for linear targets).

The earlier development already provides, for an arbitrary finite indexed
linear CFG:

* exact language preservation through raw epsilon/unit preprocessing;
* a concrete finite linear-spine terminal/binary normalization;
* an explicit polynomial size envelope for that normalized grammar; and
* the linear-spine canonical-witness theorem.

Here those pieces are composed directly, so no "already preprocessed"
hypothesis remains in the characteristic-data theorem.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z

section IndexedLinearCharacteristicData

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {M : Type z}
variable [Monoid M] [Fintype M]
variable [Fintype N] [Fintype α] [Fintype P]

/-- Canonical sample attached to the concrete normalization of an arbitrary
finite indexed linear CFG. -/
noncomputable def indexedLinearCanonicalSample
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    Finset (Word α) :=
  concreteLinearCanonicalSample
    H
    (LinearConstructedTerminalRule
      (G.linearPreparedGrammar hlinear))
    (LinearConstructedBinaryRule
      (G.linearPreparedGrammar hlinear))
    (linearConstructedStartRule
      (G.linearPreparedGrammar hlinear) S)
    (G.linearKeepEmpty hlinear S)

/-- One explicit source-only envelope for the linear characteristic sample. -/
def indexedLinearCharacteristicEnvelope
    (m n : Nat) : Nat :=
  linearSourceCharacteristicEnvelope
    m (2 * linearPreparedEncodingEnvelope n)

set_option maxHeartbeats 800000 in
/-- The composition expands several finite subtype cardinality bounds, so this
paper-facing package is given a larger elaboration budget. -/
theorem indexedLinear_characteristic_package
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules S)) :
    BatchLanguage H
        (indexedLinearCanonicalSample H G hlinear S)
      =
    LeastClosedLanguage G.toMixedRules S
    ∧
    (∑ word ∈
      indexedLinearCanonicalSample H G hlinear S,
      (word.length + 1))
      ≤
    indexedLinearCharacteristicEnvelope
      (Fintype.card M)
      G.linearNormalizationSourceScale := by
  let Gp :=
    G.linearPreparedGrammar hlinear
  let gBound :=
    2 *
      linearPreparedEncodingEnvelope
        G.linearNormalizationSourceScale

  have hlang :
      UntypedStartLanguage
          (LinearConstructedTerminalRule Gp)
          (LinearConstructedBinaryRule Gp)
          (linearConstructedStartRule Gp S)
          (G.linearKeepEmpty hlinear S)
        =
      LeastClosedLanguage G.toMixedRules S := by
    simpa only [Gp] using
      indexedLinear_normalization_language_eq
        G hlinear S

  have hshape :
      UntypedLinearSpineShape
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (LinearConstructedWrapper Gp) := by
    simpa [Gp] using
      indexedLinear_normalization_shape
        G hlinear

  have hsubNorm :
      FixedHSubstitutable H
        (UntypedStartLanguage
          (LinearConstructedTerminalRule Gp)
          (LinearConstructedBinaryRule Gp)
          (linearConstructedStartRule Gp S)
          (G.linearKeepEmpty hlinear S)) := by
    rw [hlang]
    exact hsub

  have hpack :=
    concreteLinear_characteristic_package_of_untyped_shape
      H
      (LinearConstructedTerminalRule Gp)
      (LinearConstructedBinaryRule Gp)
      (linearConstructedStartRule Gp S)
      (G.linearKeepEmpty hlinear S)
      (LinearConstructedWrapper Gp)
      hshape hsubNorm

  have hsize :
      Fintype.card (LinearConstructedState Gp)
        +
      (Fintype.card
          (LinearConstructedTerminalRuleIndex Gp)
        +
       Fintype.card
          (LinearConstructedBinaryRuleIndex Gp))
        ≤
      gBound := by
    dsimp [Gp, gBound]
    exact
      indexedLinear_normalization_size_le
        G hlinear

  have hN :
      Fintype.card (LinearConstructedState Gp)
        ≤ gBound := by
    omega

  have halpha :
      Fintype.card α ≤ gBound := by
    dsimp [gBound]
    unfold IndexedMixedCFG.linearNormalizationSourceScale
    unfold linearPreparedEncodingEnvelope
    omega

  have ht0 :=
    untypedTerminalRuleIndex_card_le_ambient
      (LinearConstructedTerminalRule Gp)
  have ht :
      (@Fintype.card
        (UntypedTerminalRuleIndex
          (LinearConstructedTerminalRule Gp))
        (Fintype.ofFinite _))
        ≤ gBound ^ 2 := by
    have hmul :
        Fintype.card (LinearConstructedState Gp) *
            Fintype.card α
          ≤
        gBound * gBound :=
      Nat.mul_le_mul hN halpha
    exact le_trans ht0
      (by simpa [pow_two] using hmul)

  have hb0 :=
    untypedBinaryRuleIndex_card_le_ambient
      (LinearConstructedBinaryRule Gp)
  have hpair :
      Fintype.card (LinearConstructedState Gp) *
          Fintype.card (LinearConstructedState Gp)
        ≤
      gBound * gBound :=
    Nat.mul_le_mul hN hN
  have htriple :
      Fintype.card (LinearConstructedState Gp) *
          (Fintype.card (LinearConstructedState Gp) *
            Fintype.card (LinearConstructedState Gp))
        ≤
      gBound * (gBound * gBound) :=
    Nat.mul_le_mul hN hpair
  have hb :
      (@Fintype.card
        (UntypedBinaryRuleIndex
          (LinearConstructedBinaryRule Gp))
        (Fintype.ofFinite _))
        ≤ gBound ^ 3 := by
    exact le_trans hb0
      (by
        simpa [pow_succ, pow_two, Nat.mul_assoc]
          using htriple)

  constructor
  · calc
      BatchLanguage H
          (indexedLinearCanonicalSample H G hlinear S)
        =
      UntypedStartLanguage
          (LinearConstructedTerminalRule Gp)
          (LinearConstructedBinaryRule Gp)
          (linearConstructedStartRule Gp S)
          (G.linearKeepEmpty hlinear S) := by
            simpa only [indexedLinearCanonicalSample, Gp]
              using hpack.1
      _ =
      LeastClosedLanguage G.toMixedRules S :=
        hlang
  · have hsample := hpack.2
    have hmono :=
      linearCharacteristicEnvelope_mono
        (m := Fintype.card M)
        hN ht hb
    have hbound :
        (∑ word ∈
          concreteLinearCanonicalSample
            H
            (LinearConstructedTerminalRule Gp)
            (LinearConstructedBinaryRule Gp)
            (linearConstructedStartRule Gp S)
            (G.linearKeepEmpty hlinear S),
          (word.length + 1))
          ≤
        linearSourceCharacteristicEnvelope
          (Fintype.card M) gBound :=
      le_trans hsample hmono
    simpa only [indexedLinearCanonicalSample,
      indexedLinearCharacteristicEnvelope,
      Gp, gBound] using hbound

end IndexedLinearCharacteristicData

end TCS1
end LeanCfgProject
