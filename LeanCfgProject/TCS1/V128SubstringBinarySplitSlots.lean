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

end ThreeCutBinary

end TCS1
end LeanCfgProject
