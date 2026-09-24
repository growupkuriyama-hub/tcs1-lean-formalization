import LeanCfgProject.TCS1.IndexedConcreteSSBNFNormalization
import LeanCfgProject.TCS1.SeparatedStartUntypedBridge
import LeanCfgProject.TCS1.CanonicalWitnessCounting

/-!
# TCS #1: concrete size bounds for the indexed normalized SSBNF grammar

This module closes the remaining cardinality bookkeeping needed to feed the
actual output of Appendix A into the Section 7 characteristic-data package.

For a finite indexed source grammar with normalization scale n, the final
productive/reachable non-start type is a subtype of the finite front-end state
type, hence has at most n states.  Its terminal rules form a subtype of
N_final × Sigma, and its binary rules form a subtype of
N_final × N_final × N_final.  Since |Sigma| <= n, all three quantities are
bounded by the explicit cubic envelope

  n + n^2 + n^3.

The bound is deliberately coarse but fully concrete and polynomial.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedNormalizationCounts

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/-- A single explicit polynomial bound for final states and both rule families. -/
def indexedSSBNFGrammarSizeEnvelope (n : Nat) : Nat :=
  n + n * n + n * (n * n)

/-- Any terminal-rule relation is no larger than its ambient N × Sigma space. -/
theorem untypedTerminalRuleIndex_card_le_product
    {N₀ : Type u} {α₀ : Type v}
    [Fintype N₀] [Fintype α₀]
    (terminalRule : N₀ → α₀ → Prop) :
    (@Fintype.card
      (UntypedTerminalRuleIndex terminalRule)
      (Fintype.ofFinite _))
      ≤
    Fintype.card N₀ * Fintype.card α₀ := by
  classical
  letI : Fintype (UntypedTerminalRuleIndex terminalRule) :=
    Fintype.ofFinite _
  have h :
      Fintype.card (UntypedTerminalRuleIndex terminalRule)
        ≤ Fintype.card (N₀ × α₀) :=
    Fintype.card_le_of_injective
      (fun p : UntypedTerminalRuleIndex terminalRule => p.1)
      Subtype.val_injective
  simpa using h

/-- Any binary-rule relation is no larger than its ambient N³ space. -/
theorem untypedBinaryRuleIndex_card_le_product
    {N₀ : Type u}
    [Fintype N₀]
    (binaryRule : N₀ → N₀ → N₀ → Prop) :
    (@Fintype.card
      (UntypedBinaryRuleIndex binaryRule)
      (Fintype.ofFinite _))
      ≤
    Fintype.card N₀ * (Fintype.card N₀ * Fintype.card N₀) := by
  classical
  letI : Fintype (UntypedBinaryRuleIndex binaryRule) :=
    Fintype.ofFinite _
  have h :
      Fintype.card (UntypedBinaryRuleIndex binaryRule)
        ≤ Fintype.card (N₀ × N₀ × N₀) :=
    Fintype.card_le_of_injective
      (fun p : UntypedBinaryRuleIndex binaryRule => p.1)
      Subtype.val_injective
  simpa [Nat.mul_assoc] using h

/-- The complete productive/reachable trim cannot increase the state count. -/
theorem reducedUnitFreeState_card_le_ambient
    {N₀ : Type u} {α₀ : Type v}
    [Fintype N₀]
    (G : BinaryNullableGrammar N₀ α₀)
    (start : ProductiveUnitFreeState G) :
    (@Fintype.card
      (ReducedUnitFreeState G start)
      (Fintype.ofFinite _))
      ≤
    Fintype.card N₀ := by
  classical
  letI : Fintype (ReducedUnitFreeState G start) :=
    Fintype.ofFinite _
  let forget :
      ReducedUnitFreeState G start → N₀ :=
    fun A => A.1.1
  have hinj : Function.Injective forget := by
    intro A B h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  exact Fintype.card_le_of_injective forget hinj

/-- The alphabet cardinality is one summand of the normalization scale. -/
theorem indexedAlphabet_card_le_normalizationScale
    (G : IndexedMixedCFG N α P) :
    Fintype.card α ≤ G.normalizationScale := by
  unfold IndexedMixedCFG.normalizationScale
  omega

/-- The actual final non-start state type has cardinality at most n_G. -/
theorem indexedReducedSSBNF_state_card_le_scale
    (G : IndexedMixedCFG N α P)
    (start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G)) :
    (@Fintype.card
      (ReducedUnitFreeState
        (indexedFiniteFrontEndGrammar G) start)
      (Fintype.ofFinite _))
      ≤
    G.normalizationScale := by
  exact le_trans
    (reducedUnitFreeState_card_le_ambient
      (indexedFiniteFrontEndGrammar G) start)
    (indexedFiniteFrontEnd_card_le_scale G)

/-- Final state count is bounded by the common cubic grammar-size envelope. -/
theorem indexedReducedSSBNF_state_card_le_grammarSizeEnvelope
    (G : IndexedMixedCFG N α P)
    (start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G)) :
    (@Fintype.card
      (ReducedUnitFreeState
        (indexedFiniteFrontEndGrammar G) start)
      (Fintype.ofFinite _))
      ≤
    indexedSSBNFGrammarSizeEnvelope G.normalizationScale := by
  have h :=
    indexedReducedSSBNF_state_card_le_scale G start
  unfold indexedSSBNFGrammarSizeEnvelope
  omega

/-- Final terminal-production count is bounded by the same cubic envelope. -/
theorem indexedReducedSSBNF_terminalRule_card_le_grammarSizeEnvelope
    (G : IndexedMixedCFG N α P)
    (start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G)) :
    (@Fintype.card
      (UntypedTerminalRuleIndex
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start))
      (Fintype.ofFinite _))
      ≤
    indexedSSBNFGrammarSizeEnvelope G.normalizationScale := by
  let Nf :=
    ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G) start
  letI : Fintype Nf := Fintype.ofFinite _
  have hraw :
      (@Fintype.card
        (UntypedTerminalRuleIndex
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
        ≤
      (@Fintype.card Nf (Fintype.ofFinite _)) *
        Fintype.card α :=
    untypedTerminalRuleIndex_card_le_product
      (reducedSSBNFTerminalRule
        (indexedFiniteFrontEndGrammar G) start)
  have hN :
      (@Fintype.card Nf (Fintype.ofFinite _))
        ≤ G.normalizationScale :=
    indexedReducedSSBNF_state_card_le_scale G start
  have hα :
      Fintype.card α ≤ G.normalizationScale :=
    indexedAlphabet_card_le_normalizationScale G
  have hprod :
      (@Fintype.card Nf (Fintype.ofFinite _)) *
          Fintype.card α
        ≤
      G.normalizationScale * G.normalizationScale :=
    Nat.mul_le_mul hN hα
  unfold indexedSSBNFGrammarSizeEnvelope
  exact le_trans hraw (le_trans hprod (by omega))

/-- Final binary-production count is bounded by the same cubic envelope. -/
theorem indexedReducedSSBNF_binaryRule_card_le_grammarSizeEnvelope
    (G : IndexedMixedCFG N α P)
    (start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G)) :
    (@Fintype.card
      (UntypedBinaryRuleIndex
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start))
      (Fintype.ofFinite _))
      ≤
    indexedSSBNFGrammarSizeEnvelope G.normalizationScale := by
  let Nf :=
    ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G) start
  letI : Fintype Nf := Fintype.ofFinite _
  have hraw :
      (@Fintype.card
        (UntypedBinaryRuleIndex
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
        ≤
      (@Fintype.card Nf (Fintype.ofFinite _)) *
        ((@Fintype.card Nf (Fintype.ofFinite _)) *
          (@Fintype.card Nf (Fintype.ofFinite _))) :=
    untypedBinaryRuleIndex_card_le_product
      (reducedSSBNFBinaryRule
        (indexedFiniteFrontEndGrammar G) start)
  have hN :
      (@Fintype.card Nf (Fintype.ofFinite _))
        ≤ G.normalizationScale :=
    indexedReducedSSBNF_state_card_le_scale G start
  have hprod :
      (@Fintype.card Nf (Fintype.ofFinite _)) *
          ((@Fintype.card Nf (Fintype.ofFinite _)) *
            (@Fintype.card Nf (Fintype.ofFinite _)))
        ≤
      G.normalizationScale *
        (G.normalizationScale * G.normalizationScale) :=
    Nat.mul_le_mul hN (Nat.mul_le_mul hN hN)
  unfold indexedSSBNFGrammarSizeEnvelope
  exact le_trans hraw (le_trans hprod (by omega))

end IndexedNormalizationCounts

end TCS1
end LeanCfgProject
