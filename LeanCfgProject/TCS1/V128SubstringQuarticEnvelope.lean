import LeanCfgProject.TCS1.V128SubstringBucketEnumeration

/-!
# TCS #1 v128: quartic direct-output envelope for the v116 candidate enumerator

This module is intentionally a SMALL DELTA from v88's already verified
ReconstructionComplexityCounts and ReconstructionFiniteCandidateSpaces.

For n_K = ||K||:
  * start candidates ≤ |K| ≤ n_K;
  * lexical/factor candidates ≤ two-cut slots ≤ n_K²;
  * binary (B) candidates ≤ three-cut slots ≤ n_K³;
  * unary (U) ordered bucket pairs ≤ n_K³, using the newly checked
    v116 occupied bucket enumeration and its injection into the
    already-checked two-cut slots;
  * an optional epsilon start candidate costs one.

Hence the concrete enumerator's candidate budget is ≤
    1 + n_K + n_K² + 2 n_K³ ≤ 4(n_K+1)³.

If each written production costs at most n_K+1 symbols, the
corresponding direct-output envelope is ≤ 4(n_K+1)^4.

IMPORTANT: This theorem counts a *sound over-approximation of the v116
rule candidates* and their uniform assumed direct-printing cost.
It is not yet a compiled executable v116 production-table algorithm
or a proof that that algorithm implements the claimed output
representation in O(n_K^4) operations. The existing v88 polynomial
construction is reused, not re-proved here.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section QuarticV116Envelope

variable {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M] [Fintype M]

/-- Explicit number of candidates scanned by the v116 rule families. -/
noncomputable def substringV116CandidateCount
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Nat :=
  1 + K.card +
    reconstructionFactorSlotCount K +
    reconstructionSplitSlotCount K +
    (∑ b ∈ substringBucketKeys H K,
      (Fintype.card
        (SubstringContextBucket H K b.1.1 b.1.2 b.2)) ^ 2)

/-- Cubic candidate-count envelope for one encoded sample norm n. -/
def substringV116CandidateEnvelope (n : Nat) : Nat :=
  1 + n + n ^ 2 + 2 * n ^ 3

/-- The concrete v116 bucket-based candidate count is at most cubic. -/
theorem substringV116CandidateCount_le_envelope
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    substringV116CandidateCount H K ≤
      substringV116CandidateEnvelope (reconstructionSampleNorm K) := by
  classical
  have hK := reconstructionSample_card_le_norm K
  have hF := reconstructionFactorSlotCount_le_sq K
  have hB := reconstructionSplitSlotCount_le_cube K
  have hU := substringBucketKeys_unaryCandidateCount_le_cube H K
  unfold substringV116CandidateCount substringV116CandidateEnvelope
  omega

/-- The candidate envelope is explicitly bounded by a cubic polynomial. -/
theorem substringV116CandidateEnvelope_le_cubic (n : Nat) :
    substringV116CandidateEnvelope n ≤ 4 * (n + 1) ^ 3 := by
  unfold substringV116CandidateEnvelope
  nlinarith [Nat.zero_le n]

/-- Concrete, key-enumeration-based v116 candidate bound. -/
theorem substringV116CandidateCount_le_cubic
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    substringV116CandidateCount H K ≤
      4 * (reconstructionSampleNorm K + 1) ^ 3 := by
  exact (substringV116CandidateCount_le_envelope H K).trans
    (substringV116CandidateEnvelope_le_cubic
      (reconstructionSampleNorm K))

/-- The budget for writing every candidate with length ≤ n_K+1. -/
noncomputable def substringV116DirectOutputBudget
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Nat :=
  substringV116CandidateCount H K * (reconstructionSampleNorm K + 1)

/-- An explicit degree-four upper bound on the candidate-printing budget. -/
theorem substringV116DirectOutputBudget_le_quartic
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    substringV116DirectOutputBudget H K ≤
      4 * (reconstructionSampleNorm K + 1) ^ 4 := by
  unfold substringV116DirectOutputBudget
  calc
    substringV116CandidateCount H K *
        (reconstructionSampleNorm K + 1) ≤
      (4 * (reconstructionSampleNorm K + 1) ^ 3) *
        (reconstructionSampleNorm K + 1) :=
      Nat.mul_le_mul_right _
        (substringV116CandidateCount_le_cubic H K)
    _ = 4 * (reconstructionSampleNorm K + 1) ^ 4 := by ring

/-- Conditional interface for a concrete emitted rule list, to be
    discharged by a later literal v116 table/encoder implementation. -/
theorem substringV116WrittenRules_le_quartic
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (productions maxWrittenRuleLength : Nat)
    (hcount : productions ≤ substringV116CandidateCount H K)
    (hmax : maxWrittenRuleLength ≤ reconstructionSampleNorm K + 1) :
    productions * maxWrittenRuleLength ≤
      4 * (reconstructionSampleNorm K + 1) ^ 4 := by
  calc
    productions * maxWrittenRuleLength ≤
        substringV116CandidateCount H K *
          (reconstructionSampleNorm K + 1) :=
      Nat.mul_le_mul hcount hmax
    _ ≤ 4 * (reconstructionSampleNorm K + 1) ^ 4 :=
      substringV116DirectOutputBudget_le_quartic H K

end QuarticV116Envelope

end TCS1
end LeanCfgProject
