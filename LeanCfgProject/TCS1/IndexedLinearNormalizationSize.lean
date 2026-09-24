import LeanCfgProject.TCS1.IndexedLinearNormalizationFacade
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# TCS #1: source-size bounds for arbitrary linear normalization

The semantic normalization chain now starts from an arbitrary finite indexed
linear CFG.  This module transports the concrete size bound all the way back
to the original indexed source encoding.

The epsilon/unit preprocessing uses at most two core-rule variants per source
production and copies them to at most every source nonterminal.  Each copied
prepared RHS is no longer than its source mixed RHS.  Consequently the total
prepared RHS length is bounded by the number of copied rules times the source
RHS total.  A coarse cubic polynomial therefore bounds the prepared encoding
scale, which is sufficient for Proposition linear-normal.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearRawFinitePreprocessingSize

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- Total mixed-symbol RHS length of a raw linear indexed grammar. -/
def RawLinearIndexedCFG.totalMixedLength
    [Fintype P]
    (G : RawLinearIndexedCFG N α P) : Nat :=
  ∑ p : P, (G.rhs p).toMixedRhs.length

/-- One source RHS length is bounded by the total raw RHS length. -/
theorem rawLinear_rhs_length_le_total
    [Fintype P]
    (G : RawLinearIndexedCFG N α P)
    (p : P) :
    (G.rhs p).toMixedRhs.length ≤
      G.totalMixedLength := by
  unfold RawLinearIndexedCFG.totalMixedLength
  exact
    Finset.single_le_sum
      (fun q _ => Nat.zero_le
        ((G.rhs q).toMixedRhs.length))
      (Finset.mem_univ p)

/--
Every core-rule variant is no longer than the source production from which it
was obtained.
-/
theorem rawLinearCoreVariantProduces_sourceLength_le
    (G : RawLinearIndexedCFG N α P)
    {slot : P × Bool}
    {rhs : PreparedLinearRhs N α}
    (hproduce :
      RawLinearCoreVariantProduces G slot rhs) :
    rhs.sourceLength ≤
      (G.rhs slot.1).toMixedRhs.length := by
  cases hproduce with
  | keep p rhs hrhs =>
      rw [hrhs]
      simp [RawLinearRhs.toMixedRhs,
        PreparedLinearRhs.toMixedRhs_length]
  | drop p left core right hnonunit hrhs hnullable =>
      rw [droppedCorePreparedRhs_sourceLength]
      rw [hrhs]
      simp [RawLinearRhs.toMixedRhs,
        PreparedLinearRhs.toMixedRhs]

/-- The chosen finite core RHS inherits the same source-length bound. -/
theorem rawLinearCorePreparedRhs_sourceLength_le
    (G : RawLinearIndexedCFG N α P)
    (q : RawLinearCoreRuleIndex G) :
    (rawLinearCorePreparedRhs G q).sourceLength ≤
      (G.rhs (rawLinearCoreRuleSource G q)).toMixedRhs.length := by
  exact
    rawLinearCoreVariantProduces_sourceLength_le
      G (rawLinearCorePreparedRhs_spec G q)

/-- Every copied prepared rule is bounded by the total raw RHS length. -/
theorem rawLinearPreparedGrammar_ruleLength_le_total
    [Fintype N] [Fintype P]
    (G : RawLinearIndexedCFG N α P)
    (q : RawLinearPreparedRuleIndex G) :
    ((rawLinearPreparedGrammar G).rhs q).sourceLength ≤
      G.totalMixedLength := by
  have hsource :=
    rawLinearCorePreparedRhs_sourceLength_le
      G q.1.2
  have htotal :=
    rawLinear_rhs_length_le_total
      G (rawLinearCoreRuleSource G q.1.2)
  exact le_trans hsource htotal

/--
The total prepared RHS length is bounded by copied-rule count times the source
RHS total.
-/
theorem rawLinearPreparedGrammar_totalSourceLength_le
    [Fintype N] [Fintype P]
    (G : RawLinearIndexedCFG N α P) :
    (rawLinearPreparedGrammar G).totalSourceLength
      ≤
    Fintype.card (RawLinearPreparedRuleIndex G) *
      G.totalMixedLength := by
  classical
  unfold PreparedLinearIndexedCFG.totalSourceLength
  calc
    (∑ q : RawLinearPreparedRuleIndex G,
        ((rawLinearPreparedGrammar G).rhs q).sourceLength)
        ≤
      ∑ _q : RawLinearPreparedRuleIndex G,
        G.totalMixedLength := by
          apply Finset.sum_le_sum
          intro q hq
          exact
            rawLinearPreparedGrammar_ruleLength_le_total
              G q
    _ =
      Fintype.card (RawLinearPreparedRuleIndex G) *
        G.totalMixedLength := by
          simp

/--
For the raw presentation chosen from an ordinary indexed linear CFG, total
mixed RHS length is exactly the original indexed RHS length.
-/
theorem indexedMixedCFG_toRawLinear_totalMixedLength
    [Fintype P]
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear) :
    (G.toRawLinear hlinear).totalMixedLength =
      G.totalRhsLength := by
  classical
  unfold RawLinearIndexedCFG.totalMixedLength
  unfold IndexedMixedCFG.totalRhsLength
  apply Finset.sum_congr rfl
  intro p hp
  change
    (indexedRawLinearRhs G hlinear p).toMixedRhs.length =
      (G.rhs p).length
  rw [indexedRawLinearRhs_toMixed]

/-- Original size scale including the terminal alphabet. -/
def IndexedMixedCFG.linearNormalizationSourceScale
    [Fintype N] [Fintype α] [Fintype P]
    (G : IndexedMixedCFG N α P) : Nat :=
  Fintype.card α + G.encodingScale

/-- Cubic envelope used for the prepared intermediate encoding. -/
def linearPreparedEncodingEnvelope
    (g : Nat) : Nat :=
  g + 2 * g ^ 2 + 2 * g ^ 3

/--
The finite prepared grammar produced by epsilon/unit preprocessing has cubic
size in the original indexed source scale.
-/
theorem indexedLinear_preparedEncodingScale_le
    [Fintype N] [Fintype α] [Fintype P]
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear) :
    (G.linearPreparedGrammar hlinear).encodingScale
      ≤
    linearPreparedEncodingEnvelope
      G.linearNormalizationSourceScale := by
  let g := G.linearNormalizationSourceScale
  let R := G.toRawLinear hlinear
  have hn : Fintype.card N ≤ g := by
    dsimp [g, IndexedMixedCFG.linearNormalizationSourceScale]
    unfold IndexedMixedCFG.encodingScale
    omega
  have ha : Fintype.card α ≤ g := by
    dsimp [g, IndexedMixedCFG.linearNormalizationSourceScale]
    omega
  have hp : Fintype.card P ≤ g := by
    dsimp [g, IndexedMixedCFG.linearNormalizationSourceScale]
    unfold IndexedMixedCFG.encodingScale
    omega
  have hr : G.totalRhsLength ≤ g := by
    dsimp [g, IndexedMixedCFG.linearNormalizationSourceScale]
    unfold IndexedMixedCFG.encodingScale
    omega
  have hnp :
      Fintype.card N * Fintype.card P
        ≤
      g * g :=
    Nat.mul_le_mul hn hp
  have hq0 :
      Fintype.card (RawLinearPreparedRuleIndex R)
        ≤
      2 * Fintype.card N * Fintype.card P :=
    rawLinearPreparedRuleIndex_card_le R
  have hq :
      Fintype.card (RawLinearPreparedRuleIndex R)
        ≤
      2 * g ^ 2 := by
    have htwo :
        2 * (Fintype.card N * Fintype.card P)
          ≤
        2 * (g * g) :=
      Nat.mul_le_mul_left 2 hnp
    calc
      Fintype.card (RawLinearPreparedRuleIndex R)
          ≤
        2 * Fintype.card N * Fintype.card P := hq0
      _ =
        2 * (Fintype.card N * Fintype.card P) := by
          rw [Nat.mul_assoc]
      _ ≤
        2 * (g * g) := htwo
      _ =
        2 * g ^ 2 := by
          simp [pow_two]
  have hrawTotal :
      R.totalMixedLength = G.totalRhsLength := by
    simpa [R] using
      indexedMixedCFG_toRawLinear_totalMixedLength
        G hlinear
  have htotal0 :
      (rawLinearPreparedGrammar R).totalSourceLength
        ≤
      Fintype.card (RawLinearPreparedRuleIndex R) *
        R.totalMixedLength :=
    rawLinearPreparedGrammar_totalSourceLength_le R
  have htotal :
      (rawLinearPreparedGrammar R).totalSourceLength
        ≤
      2 * g ^ 3 := by
    have hmul :
        Fintype.card (RawLinearPreparedRuleIndex R) *
            R.totalMixedLength
          ≤
        (2 * g ^ 2) * g := by
      apply Nat.mul_le_mul hq
      rw [hrawTotal]
      exact hr
    calc
      (rawLinearPreparedGrammar R).totalSourceLength
          ≤
        Fintype.card (RawLinearPreparedRuleIndex R) *
          R.totalMixedLength := htotal0
      _ ≤
        (2 * g ^ 2) * g := hmul
      _ =
        2 * g ^ 3 := by
          ring
  have hbase :
      Fintype.card N + Fintype.card α ≤ g := by
    dsimp [g, IndexedMixedCFG.linearNormalizationSourceScale]
    unfold IndexedMixedCFG.encodingScale
    omega
  change
    Fintype.card N + Fintype.card α +
        Fintype.card (RawLinearPreparedRuleIndex R) +
        (rawLinearPreparedGrammar R).totalSourceLength
      ≤
    linearPreparedEncodingEnvelope g
  unfold linearPreparedEncodingEnvelope
  omega

/--
The actual concrete linear-spine grammar therefore has a polynomial source
size bound, with no intermediate grammar counts left in the statement.
-/
theorem indexedLinear_constructedSize_le_sourceEnvelope
    [Fintype N] [Fintype α] [Fintype P]
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear) :
    Fintype.card
        (LinearConstructedState
          (G.linearPreparedGrammar hlinear))
      +
      (Fintype.card
          (LinearConstructedTerminalRuleIndex
            (G.linearPreparedGrammar hlinear))
       +
       Fintype.card
          (LinearConstructedBinaryRuleIndex
            (G.linearPreparedGrammar hlinear)))
      ≤
    2 *
      linearPreparedEncodingEnvelope
        G.linearNormalizationSourceScale := by
  have hconstructed :=
    linearConstructed_combined_size_le_twice_scale
      (G.linearPreparedGrammar hlinear)
  have hprepared :=
    indexedLinear_preparedEncodingScale_le
      G hlinear
  exact
    le_trans hconstructed
      (Nat.mul_le_mul_left 2 hprepared)

end LinearRawFinitePreprocessingSize

end TCS1
end LeanCfgProject
