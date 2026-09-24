import LeanCfgProject.TCS1.IndexedPreprocessedLinearCharacteristicData

/-!
# TCS #1: source-size polynomial envelope for linear characteristic data

The linear characteristic theorem is naturally stated using the actual
normalized state, terminal-rule, and binary-rule counts.  This module removes
those internal counts.

For any finite terminal/binary grammar, terminal rules form a subtype of
N x Sigma and binary rules a subtype of N x N x N.  Hence a normalized state
bound g immediately gives coarse rule bounds g^2 and g^3 once the alphabet is
also bounded by g.

The specialized linear normalization has exactly such a state bound with
g equal to its prepared encoding scale.  Consequently the characteristic
sample of the original preprocessed indexed linear CFG has an explicit
polynomial envelope depending only on the fixed monoid size and source
encoding scale.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z

section LinearCharacteristicSourceBounds

variable {X : Type u}
variable {α : Type v}

/-- Any terminal-rule predicate has at most |X|*|Sigma| distinct rules. -/
theorem untypedTerminalRuleIndex_card_le_ambient
    [Fintype X] [Fintype α]
    (terminalRule : X → α → Prop) :
    @Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _)
      ≤
    Fintype.card X * Fintype.card α := by
  letI : Fintype (UntypedTerminalRuleIndex terminalRule) :=
    Fintype.ofFinite _
  calc
    Fintype.card (UntypedTerminalRuleIndex terminalRule)
        ≤ Fintype.card (X × α) :=
      Fintype.card_subtype_le _
    _ = Fintype.card X * Fintype.card α := by
      simp

/-- Any binary-rule predicate has at most |X|^3 distinct rules. -/
theorem untypedBinaryRuleIndex_card_le_ambient
    [Fintype X]
    (binaryRule : X → X → X → Prop) :
    @Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _)
      ≤
    Fintype.card X *
      (Fintype.card X * Fintype.card X) := by
  letI : Fintype (UntypedBinaryRuleIndex binaryRule) :=
    Fintype.ofFinite _
  calc
    Fintype.card (UntypedBinaryRuleIndex binaryRule)
        ≤ Fintype.card (X × X × X) :=
      Fintype.card_subtype_le _
    _ =
      Fintype.card X *
        (Fintype.card X * Fintype.card X) := by
      simp

/--
The linear characteristic envelope is monotone in state and rule counts when
the fixed monoid size is held constant.
-/
theorem linearCharacteristicEnvelope_mono
    {m N t b N' t' b' : Nat}
    (hN : N ≤ N')
    (ht : t ≤ t')
    (hb : b ≤ b') :
    linearCharacteristicEnvelope m N t b ≤
      linearCharacteristicEnvelope m N' t' b' := by
  have hNm :
      N * m ≤ N' * m :=
    Nat.mul_le_mul_right m hN
  have hbm :
      b * m ^ 2 ≤ b' * m ^ 2 :=
    Nat.mul_le_mul_right (m ^ 2) hb
  have hcount :
      witnessCountEnvelope N t b m ≤
        witnessCountEnvelope N' t' b' m := by
    unfold witnessCountEnvelope
    unfold typedNonterminalCountEnvelope
    unfold typedRuleCountEnvelope
    omega
  have hlen :
      linearCanonicalWitnessLengthEnvelope (N * m) + 1
        ≤
      linearCanonicalWitnessLengthEnvelope (N' * m) + 1 := by
    exact
      Nat.add_le_add_right
        (linearCanonicalWitnessLengthEnvelope_mono hNm) 1
  unfold linearCharacteristicEnvelope
  exact Nat.mul_le_mul hcount hlen

/-- Coarse source-only polynomial envelope for the linear characteristic set. -/
def linearSourceCharacteristicEnvelope
    (m g : Nat) : Nat :=
  linearCharacteristicEnvelope
    m g (g ^ 2) (g ^ 3)

/--
For the actual specialized linear normalization, the internal characteristic
envelope is bounded by the source-scale envelope.
-/
theorem preparedLinear_characteristicEnvelope_le_sourceScale
    {N : Type u}
    {P : Type w}
    {M : Type z}
    [Monoid M] [Fintype M]
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    linearCharacteristicEnvelope
      (Fintype.card M)
      (Fintype.card (LinearConstructedState G))
      (@Fintype.card
        (UntypedTerminalRuleIndex
          (LinearConstructedTerminalRule G))
        (Fintype.ofFinite _))
      (@Fintype.card
        (UntypedBinaryRuleIndex
          (LinearConstructedBinaryRule G))
        (Fintype.ofFinite _))
      ≤
    linearSourceCharacteristicEnvelope
      (Fintype.card M) G.encodingScale := by
  let g := G.encodingScale
  have hstate :
      Fintype.card (LinearConstructedState G) ≤ g := by
    simpa [g] using
      (linearConstructedState_card_le_scale G)
  have halpha :
      Fintype.card α ≤ g := by
    dsimp [g]
    unfold PreparedLinearIndexedCFG.encodingScale
    omega
  have hterm0 :=
    untypedTerminalRuleIndex_card_le_ambient
      (LinearConstructedTerminalRule G)
  have hterm :
      @Fintype.card
          (UntypedTerminalRuleIndex
            (LinearConstructedTerminalRule G))
          (Fintype.ofFinite _)
        ≤
      g ^ 2 := by
    have hmul :
        Fintype.card (LinearConstructedState G) *
            Fintype.card α
          ≤
        g * g :=
      Nat.mul_le_mul hstate halpha
    exact le_trans hterm0 (by simpa [pow_two] using hmul)
  have hbin0 :=
    untypedBinaryRuleIndex_card_le_ambient
      (LinearConstructedBinaryRule G)
  have hpair :
      Fintype.card (LinearConstructedState G) *
          Fintype.card (LinearConstructedState G)
        ≤
      g * g :=
    Nat.mul_le_mul hstate hstate
  have htriple :
      Fintype.card (LinearConstructedState G) *
          (Fintype.card (LinearConstructedState G) *
            Fintype.card (LinearConstructedState G))
        ≤
      g * (g * g) :=
    Nat.mul_le_mul hstate hpair
  have hbin :
      @Fintype.card
          (UntypedBinaryRuleIndex
            (LinearConstructedBinaryRule G))
          (Fintype.ofFinite _)
        ≤
      g ^ 3 := by
    exact le_trans hbin0
      (by
        simpa [pow_succ, pow_two, Nat.mul_assoc]
          using htriple)
  unfold linearSourceCharacteristicEnvelope
  exact
    linearCharacteristicEnvelope_mono
      hstate hterm hbin

/--
Paper-facing polynomial sample bound expressed only in the original indexed
preprocessed linear CFG scale.
-/
theorem indexedPreprocessedLinear_characteristic_sample_sourceBound
    {N : Type u}
    {P : Type w}
    {M : Type z}
    [Monoid M] [Fintype M]
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (hprep : IndexedLinearPreprocessed G)
    (S : N)
    (keepEmpty : Prop)
    (hsub :
      FixedHSubstitutable H
        (G.linearTargetLanguage S keepEmpty)) :
    (∑ word ∈
      indexedPreprocessedLinearCanonicalSample
        H G hprep S keepEmpty,
      (word.length + 1))
      ≤
    linearSourceCharacteristicEnvelope
      (Fintype.card M)
      G.linearPreparedScale := by
  have hsample :=
    (indexedPreprocessedLinear_characteristic_package
      H G hprep S keepEmpty hsub).2
  have henvelope :=
    preparedLinear_characteristicEnvelope_le_sourceScale
      (M := M) (G.toPreparedLinear hprep)
  have hscale :
      (G.toPreparedLinear hprep).encodingScale =
        G.linearPreparedScale :=
    indexedMixedCFG_toPreparedLinear_encodingScale
      G hprep
  calc
    (∑ word ∈
      indexedPreprocessedLinearCanonicalSample
        H G hprep S keepEmpty,
      (word.length + 1))
      ≤
    linearCharacteristicEnvelope
      (Fintype.card M)
      (Fintype.card
        (LinearConstructedState
          (G.toPreparedLinear hprep)))
      (@Fintype.card
        (UntypedTerminalRuleIndex
          (LinearConstructedTerminalRule
            (G.toPreparedLinear hprep)))
        (Fintype.ofFinite _))
      (@Fintype.card
        (UntypedBinaryRuleIndex
          (LinearConstructedBinaryRule
            (G.toPreparedLinear hprep)))
        (Fintype.ofFinite _)) := hsample
    _ ≤
      linearSourceCharacteristicEnvelope
        (Fintype.card M)
        (G.toPreparedLinear hprep).encodingScale :=
      henvelope
    _ =
      linearSourceCharacteristicEnvelope
        (Fintype.card M)
        G.linearPreparedScale := by
      rw [hscale]

end LinearCharacteristicSourceBounds

end TCS1
end LeanCfgProject
