import LeanCfgProject.TCS1.V128SubstringTabulatedGrammar
import Mathlib.Tactic

/-!
# TCS #1 v128: three-cut candidate cover for literal (B) rules

Unlike the broad triple-state filter, the candidate generator here is
indexed by the archived ReconstructionSplitSlot K: a sample word and
three cuts. This finite type was already proved to have cardinality
at most ||K||^3, and so is a correct polynomial-sized candidate
universe for v116 binary rules.

This file first verifies that every actual v116 binary production
is decoded by a three-cut occurrence. The raw slot decoder can also
produce empty/reversed/otherwise invalid candidates; hence the
unfiltered image is *not* asserted to be the actual production table.
Filtering and executable output costs are separate work.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ThreeCutBinary

variable {α : Type u} {M : Type v}
variable [Fintype α] [DecidableEq α] [Monoid M] [Fintype M]

/-- Decode a sample triple-cut index to its potential parent/children
    word identifiers. The three cut positions need not be ordered. -/
def v116BinarySplitCode
    {K : Finset (Word α)}
    (s : ReconstructionSplitSlot K) :
    Word α × (Word α × Word α) :=
  let w := s.1.1
  let i := s.2.1.1
  let j := s.2.2.1.1
  let k := s.2.2.2.1
  ((w.drop i).take (k - i),
   ((w.drop i).take (j - i),
    (w.drop j).take (k - j)))

/-- The finite raw three-cut candidate set; candidates with invalid
    splits are harmless but must not be emitted unfiltered. -/
noncomputable def v116BinarySplitCodes
    (K : Finset (Word α)) :
    Finset (Word α × (Word α × Word α)) := by
  classical
  exact Finset.univ.image (v116BinarySplitCode (K := K))

/-- An existing (B) rule can always be located using a sample word
    containing the parent and the cuts around both children. -/
theorem v116BinarySplitCodes_cover
    (K : Finset (Word α))
    (A B C : ObservedSubstringNonterminal K)
    (h : A.1 = B.1 ++ C.1) :
    (A.1, (B.1, C.1)) ∈ v116BinarySplitCodes K := by
  classical
  rcases A.2 with ⟨p, q, hobs⟩
  let w : Word α := p ++ B.1 ++ C.1 ++ q
  have hw : w ∈ K := by
    simpa [w, h, List.append_assoc] using hobs.2
  have hi : p.length < w.length + 1 := by
    simp only [w, List.length_append]
    omega
  have hj : p.length + B.1.length < w.length + 1 := by
    simp only [w, List.length_append]
    omega
  have hk : p.length + B.1.length + C.1.length <
      w.length + 1 := by
    simp only [w, List.length_append]
    omega
  let s : ReconstructionSplitSlot K :=
    ⟨⟨w, hw⟩,
      (⟨p.length, hi⟩,
        (⟨p.length + B.1.length, hj⟩,
          ⟨p.length + B.1.length + C.1.length, hk⟩))⟩
  unfold v116BinarySplitCodes
  apply Finset.mem_image.mpr
  refine ⟨s, Finset.mem_univ _, ?_⟩
  simp [v116BinarySplitCode, s, w, h, List.append_assoc]
  have hlen :
      p.length + B.1.length + C.1.length - p.length =
        B.1.length + C.1.length := by omega
  rw [hlen]
  simp [List.append_assoc]

/-- Every candidate index in the raw triple-cut space is already
    controlled by the previously verified cubic sample bound. -/
theorem v116BinarySplitCodes_card_le_cube
    (K : Finset (Word α)) :
    (v116BinarySplitCodes K).card ≤
      (reconstructionSampleNorm K) ^ 3 := by
  classical
  calc
    (v116BinarySplitCodes K).card ≤
        Fintype.card (ReconstructionSplitSlot K) := by
      unfold v116BinarySplitCodes
      simpa using (Finset.card_image_le
        (s := (Finset.univ : Finset (ReconstructionSplitSlot K)))
        (f := v116BinarySplitCode (K := K)))
    _ ≤ (reconstructionSampleNorm K) ^ 3 :=
      reconstructionSplitSlot_card_le_cube K


/-- Turn an actual finite v116 binary production into its word-indexed
    triple. The observed-factor states have unique names, so this loses
    no information. -/
def v116BinaryProductionWordCode
    {K : Finset (Word α)}
    (e : V116BinaryEntry K) :
    Word α × (Word α × Word α) :=
  (e.1.1, (e.2.1.1, e.2.2.1))

theorem v116BinaryProductionWordCode_injective
    (K : Finset (Word α)) :
    Function.Injective (v116BinaryProductionWordCode (K := K)) := by
  intro e f heq
  rcases e with ⟨A, B, C⟩
  rcases f with ⟨D, E, F⟩
  change (A.1, (B.1, C.1)) = (D.1, (E.1, F.1)) at heq
  have hA : A = D := Subtype.ext (congrArg Prod.fst heq)
  have hBC : (B.1, C.1) = (E.1, F.1) :=
    congrArg Prod.snd heq
  have hB : B = E := Subtype.ext (congrArg Prod.fst hBC)
  have hC : C = F := Subtype.ext (congrArg Prod.snd hBC)
  cases hA
  cases hB
  cases hC
  rfl

/-- A finite type of actual binary productions, not all three-state
    tuples. -/
abbrev V116ActualBinaryRule (K : Finset (Word α)) :=
  {e : V116BinaryEntry K // e ∈ v116BinaryRuleTable K}

noncomputable instance v116ActualBinaryRuleFintype
    (K : Finset (Word α)) :
    Fintype (V116ActualBinaryRule K) := by
  classical
  infer_instance

/-- Each *actual* (B) rule has a three-cut sample slot that decodes
    exactly to its parent/children word triple. -/
theorem v116ActualBinaryRule_has_split_slot
    (K : Finset (Word α))
    (e : V116ActualBinaryRule K) :
    ∃ s : ReconstructionSplitSlot K,
      v116BinarySplitCode s = v116BinaryProductionWordCode e.1 := by
  classical
  have hbin : e.1.1.1 = e.1.2.1.1 ++ e.1.2.2.1 := by
    simpa [v116BinaryRuleTable] using e.2
  have hcover :=
    v116BinarySplitCodes_cover K e.1.1 e.1.2.1 e.1.2.2 hbin
  unfold v116BinarySplitCodes at hcover
  rcases Finset.mem_image.mp hcover with ⟨s, _, hs⟩
  exact ⟨s, hs⟩

/-- Choose a representative sample and three cuts for each actual
    binary rule. This selection is still noncomputable. -/
noncomputable def v116ActualBinaryRuleToSplitSlot
    (K : Finset (Word α))
    (e : V116ActualBinaryRule K) :
    ReconstructionSplitSlot K :=
  Classical.choose (v116ActualBinaryRule_has_split_slot K e)

theorem v116ActualBinaryRuleToSplitSlot_code
    (K : Finset (Word α))
    (e : V116ActualBinaryRule K) :
    v116BinarySplitCode (v116ActualBinaryRuleToSplitSlot K e) =
      v116BinaryProductionWordCode e.1 :=
  Classical.choose_spec (v116ActualBinaryRule_has_split_slot K e)

/-- Different actual rules cannot use the same selected three-cut
    slot: that slot determines the complete word triple. -/
theorem v116ActualBinaryRuleToSplitSlot_injective
    (K : Finset (Word α)) :
    Function.Injective (v116ActualBinaryRuleToSplitSlot K) := by
  intro e f heq
  apply Subtype.ext
  apply v116BinaryProductionWordCode_injective K
  calc
    v116BinaryProductionWordCode e.1 =
        v116BinarySplitCode (v116ActualBinaryRuleToSplitSlot K e) :=
      (v116ActualBinaryRuleToSplitSlot_code K e).symm
    _ = v116BinarySplitCode (v116ActualBinaryRuleToSplitSlot K f) := by
      rw [heq]
    _ = v116BinaryProductionWordCode f.1 :=
      v116ActualBinaryRuleToSplitSlot_code K f

/-- **Unconditional cubic bound on the actual (B) production table**.
    This uses the verified cardinality of old three-cut candidate slots
    and needs no extra production-count assumption. It does not, by
    itself, give a runtime bound for constructing or deduplicating
    the table. -/
theorem v116BinaryRuleTable_card_le_cube
    (K : Finset (Word α)) :
    (v116BinaryRuleTable K).card ≤
      (reconstructionSampleNorm K) ^ 3 := by
  classical
  have hcard :
      Fintype.card (V116ActualBinaryRule K) ≤
        Fintype.card (ReconstructionSplitSlot K) :=
    Fintype.card_le_of_injective
      (v116ActualBinaryRuleToSplitSlot K)
      (v116ActualBinaryRuleToSplitSlot_injective K)
  have htable :
      Fintype.card (V116ActualBinaryRule K) =
        (v116BinaryRuleTable K).card := by
    simpa [V116ActualBinaryRule] using
      (Fintype.card_coe (v116BinaryRuleTable K))
  rw [htable] at hcard
  exact hcard.trans (reconstructionSplitSlot_card_le_cube K)

end ThreeCutBinary

end TCS1
end LeanCfgProject
