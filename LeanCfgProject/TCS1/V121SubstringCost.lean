import LeanCfgProject.TCS1.V121SubstringReconstruction
import LeanCfgProject.TCS1.ReconstructionFactorSlotState
import Mathlib.Tactic

/-!
# TCS #1 v121: distinct-substring state counting and bucket inequality

This module checks two numeric ingredients of the v121 *new*
substring-indexed reconstruction argument:

* the distinct observed nonempty factors inject into the image of a
  computable finite occurrence-slot enumeration of quadratic size;
* the bucket square-sum calculation that converts O(n²) total entries
  and O(n) entries per bucket into O(n³) ordered-pair candidates.

The bucket bounds must still be connected to the *exact v121 (u,v,h) bucket
enumerator*; this file does not claim that the complete explicit O(n^4)
writing-time theorem has been formalized.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V121SubstringCost

variable {α : Type u}
variable [DecidableEq α]

/-- A finite computable superset of all distinct observed factors, formed
from exactly the two-cut occurrence slots of the archived implementation. -/
def v121FactorCandidates (K : Finset (Word α)) : Finset (Word α) :=
  (Finset.univ : Finset (ReconstructionFactorSlot K)).image
    (fun s => (reconstructionFactorSlotNonterminal s).factor)

/-- Every substring state of the v121 paper has a representative in the
executable occurrence-slot state space. -/
theorem v121_observed_mem_candidates
    (K : Finset (Word α))
    {x : Word α}
    (hx : SubstringObserved K x) :
    x ∈ v121FactorCandidates K := by
  rcases hx with ⟨u, v, hobs⟩
  apply Finset.mem_image.mpr
  refine ⟨observedReconstructionFactorSlot K hobs, Finset.mem_univ _, ?_⟩
  simpa only [reconstructionFactorSlotNonterminal_observed]

/-- Finite quotient distinct-substring *state upper bound*: at most n_K². -/
theorem v121_factorCandidates_card_le_sq
    (K : Finset (Word α)) :
    (v121FactorCandidates K).card ≤
      (reconstructionSampleNorm K) ^ 2 := by
  calc
    (v121FactorCandidates K).card ≤
        (Finset.univ : Finset (ReconstructionFactorSlot K)).card := by
          exact Finset.card_image_le
    _ = Fintype.card (ReconstructionFactorSlot K) := by simp
    _ ≤ (reconstructionSampleNorm K) ^ 2 :=
          reconstructionFactorSlot_card_le_sq K

/-- General finite-bucket inequality: sum of bucket-square sizes is at most
maximum bucket size times the total number of entries. -/
theorem v121_sum_bucket_squares
    {ι : Type v}
    (buckets : Finset ι)
    (bucket : ι → Finset (Word α))
    (cap : Nat)
    (hcap : ∀ i ∈ buckets, (bucket i).card ≤ cap) :
    (∑ i ∈ buckets, (bucket i).card ^ 2) ≤
      cap * (∑ i ∈ buckets, (bucket i).card) := by
  calc
    (∑ i ∈ buckets, (bucket i).card ^ 2)
        ≤ ∑ i ∈ buckets, cap * (bucket i).card := by
            apply Finset.sum_le_sum
            intro i hi
            have hle := hcap i hi
            nlinarith [Nat.mul_le_mul_right (bucket i).card hle]
    _ = cap * (∑ i ∈ buckets, (bucket i).card) := by
          rw [Finset.mul_sum]

/-- The polynomial step used for v121 unary-rule buckets. If each
context/type bucket has at most |K| entries and the sum of bucket entries
is at most n_K², then ordered-pair emissions are bounded by n_K³. -/
theorem v121_bucket_emissions_le_cube
    {ι : Type v}
    (K : Finset (Word α))
    (buckets : Finset ι)
    (bucket : ι → Finset (Word α))
    (hcap : ∀ i ∈ buckets, (bucket i).card ≤ K.card)
    (htotal :
      (∑ i ∈ buckets, (bucket i).card) ≤
        (reconstructionSampleNorm K) ^ 2) :
    (∑ i ∈ buckets, (bucket i).card ^ 2) ≤
      (reconstructionSampleNorm K) ^ 3 := by
  calc
    (∑ i ∈ buckets, (bucket i).card ^ 2)
        ≤ K.card * (∑ i ∈ buckets, (bucket i).card) :=
          v121_sum_bucket_squares buckets bucket K.card hcap
    _ ≤ (reconstructionSampleNorm K) *
        (reconstructionSampleNorm K) ^ 2 := by
          exact Nat.mul_le_mul
            (reconstructionSample_card_le_norm K) htotal
    _ = (reconstructionSampleNorm K) ^ 3 := by ring

end V121SubstringCost

end TCS1
end LeanCfgProject
