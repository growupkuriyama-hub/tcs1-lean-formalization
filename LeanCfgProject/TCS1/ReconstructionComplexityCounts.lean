import LeanCfgProject.TCS1.ReconstructionSoundness
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# TCS #1: polynomial counting for the reconstruction step

This file verifies the combinatorial core of Section "Complexity of the
Reconstruction Step" of the revised manuscript.

For a finite positive sample K we use exactly the paper's encoded sample norm

  ||K|| = sum_{w in K} (|w| + 1).

A word of length m has at most (m+1)^2 pairs of cut positions, which generously
cover all factorizations u x v, and at most (m+1)^3 triples of cut positions,
which generously cover the candidates used by the binary reconstruction rule.
Summing over the sample gives quadratic and cubic bounds in ||K||.  Pairing
observed nonterminals then gives a quartic candidate space for Rules R2/R3.

The final explicit envelope below has degree five after multiplying the number
of rule candidates by an O(||K||) direct string encoding per production.  This
is the arithmetic/counting content of Theorem (poly-build); an executable
enumerator and machine-cost model are deliberately kept separate.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section ReconstructionComplexityCounts

variable {α : Type u}

/-- The encoded positive-sample size used in the manuscript. -/
def reconstructionSampleNorm
    (K : Finset (Word α)) : Nat :=
  ∑ w ∈ K, (w.length + 1)

/-- A generous count of two-cut slots across all sample words. -/
def reconstructionFactorSlotCount
    (K : Finset (Word α)) : Nat :=
  ∑ w ∈ K, (w.length + 1) ^ 2

/-- A generous count of three-cut slots across all sample words. -/
def reconstructionSplitSlotCount
    (K : Finset (Word α)) : Nat :=
  ∑ w ∈ K, (w.length + 1) ^ 3

/-- Sum of squares is bounded by the square of the sum over naturals. -/
theorem finset_sum_sq_le_sq_sum
    {β : Type*}
    (s : Finset β)
    (f : β → Nat) :
    (∑ x ∈ s, (f x) ^ 2) ≤
      (∑ x ∈ s, f x) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert, ha, not_false_eq_true,
        pow_two] at ih ⊢
      let A := f a
      let S := ∑ x ∈ s, f x
      let Q := ∑ x ∈ s, f x * f x
      have hbase : A * A + Q ≤ A * A + S * S := by
        exact Nat.add_le_add_left ih (A * A)
      have hcross :
          A * A + S * S ≤
            A * A + S * S + 2 * (A * S) := by
        omega
      calc
        A * A + Q ≤ A * A + S * S := hbase
        _ ≤ A * A + S * S + 2 * (A * S) := hcross
        _ = (A + S) * (A + S) := by ring

/-- Sum of cubes is bounded by the cube of the sum over naturals. -/
theorem finset_sum_cube_le_cube_sum
    {β : Type*}
    (s : Finset β)
    (f : β → Nat) :
    (∑ x ∈ s, (f x) ^ 3) ≤
      (∑ x ∈ s, f x) ^ 3 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, pow_succ] at ih ⊢
      let A := f a
      let S := ∑ x ∈ s, f x
      let Q := ∑ x ∈ s, f x * f x * f x
      change A * A * A + Q ≤
        (A + S) * (A + S) * (A + S)
      have ih' : Q ≤ S * S * S := by
        simpa [Q, S, Nat.mul_assoc] using ih
      have hbase :
          A * A * A + Q ≤
            A * A * A + S * S * S :=
        Nat.add_le_add_left ih' (A * A * A)
      have hcross :
          A * A * A + S * S * S ≤
            A * A * A + S * S * S +
              3 * (A * A * S) +
              3 * (A * S * S) := by
        omega
      calc
        A * A * A + Q
            ≤ A * A * A + S * S * S := hbase
        _ ≤ A * A * A + S * S * S +
              3 * (A * A * S) +
              3 * (A * S * S) := hcross
        _ = (A + S) * (A + S) * (A + S) := by ring

/-- The number of distinct sample words is at most the encoded sample norm. -/
theorem reconstructionSample_card_le_norm
    (K : Finset (Word α)) :
    K.card ≤ reconstructionSampleNorm K := by
  classical
  unfold reconstructionSampleNorm
  induction K using Finset.induction_on with
  | empty =>
      simp
  | @insert w K hw ih =>
      simp [hw]
      omega

/--
Across all sample words, the generous factor/context slot count is quadratic
in the encoded sample norm.
-/
theorem reconstructionFactorSlotCount_le_sq
    (K : Finset (Word α)) :
    reconstructionFactorSlotCount K ≤
      (reconstructionSampleNorm K) ^ 2 := by
  unfold reconstructionFactorSlotCount reconstructionSampleNorm
  exact
    finset_sum_sq_le_sq_sum
      K (fun w : Word α => w.length + 1)

/--
Across all sample words, the generous binary-split slot count is cubic in the
encoded sample norm.
-/
theorem reconstructionSplitSlotCount_le_cube
    (K : Finset (Word α)) :
    reconstructionSplitSlotCount K ≤
      (reconstructionSampleNorm K) ^ 3 := by
  unfold reconstructionSplitSlotCount reconstructionSampleNorm
  exact
    finset_sum_cube_le_cube_sum
      K (fun w : Word α => w.length + 1)

/--
Pairs of observed-factor slots, the candidate space used by Rules R2 and R3,
are bounded quartically.
-/
theorem reconstructionFactorPairCount_le_fourth
    (K : Finset (Word α)) :
    reconstructionFactorSlotCount K *
        reconstructionFactorSlotCount K
      ≤
    (reconstructionSampleNorm K) ^ 4 := by
  have h :=
    Nat.mul_le_mul
      (reconstructionFactorSlotCount_le_sq K)
      (reconstructionFactorSlotCount_le_sq K)
  simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using h

/--
A paper-facing generous candidate envelope.

The summands cover, respectively, start candidates, terminal/factor candidates,
R1 split candidates, and the two pair-based rule families R2/R3.
-/
def reconstructionRuleCandidateEnvelope
    (n : Nat) : Nat :=
  n + n ^ 2 + n ^ 3 + 2 * n ^ 4

/--
The concrete candidate counts used in the paper are bounded by the explicit
quartic envelope.
-/
theorem reconstruction_rule_candidates_le
    (K : Finset (Word α)) :
    K.card +
        reconstructionFactorSlotCount K +
        reconstructionSplitSlotCount K +
        2 *
          (reconstructionFactorSlotCount K *
            reconstructionFactorSlotCount K)
      ≤
    reconstructionRuleCandidateEnvelope
      (reconstructionSampleNorm K) := by
  have h0 := reconstructionSample_card_le_norm K
  have h2 := reconstructionFactorSlotCount_le_sq K
  have h3 := reconstructionSplitSlotCount_le_cube K
  have h4 := reconstructionFactorPairCount_le_fourth K
  unfold reconstructionRuleCandidateEnvelope
  omega

/--
The number of cached substring h-values is also covered by the quadratic
factor-slot bound.
-/
theorem reconstruction_cached_h_values_le_sq
    (K : Finset (Word α))
    (cached : Nat)
    (hcached :
      cached ≤ reconstructionFactorSlotCount K) :
    cached ≤ (reconstructionSampleNorm K) ^ 2 :=
  le_trans hcached (reconstructionFactorSlotCount_le_sq K)

/--
Explicit direct-encoding envelope for the output grammar.  Its highest-degree
term is quartic candidate count times a linear production encoding, hence
degree five in the sample norm.
-/
def reconstructionOutputEncodingEnvelope
    (n : Nat) : Nat :=
  reconstructionRuleCandidateEnvelope n * (n + 1)

/-- The quartic candidate expression has a simple uniform polynomial bound. -/
theorem reconstructionRuleCandidateEnvelope_le
    (n : Nat) :
    reconstructionRuleCandidateEnvelope n ≤
      5 * (n + 1) ^ 4 := by
  unfold reconstructionRuleCandidateEnvelope
  nlinarith [Nat.zero_le n]

/--
The explicit direct-output envelope is bounded by a single degree-five
polynomial.  This is a literal polynomial majorant for the manuscript's
O(n_K^5) statement.
-/
theorem reconstructionOutputEncodingEnvelope_le_degreeFive
    (n : Nat) :
    reconstructionOutputEncodingEnvelope n ≤
      5 * (n + 1) ^ 5 := by
  unfold reconstructionOutputEncodingEnvelope
  have h :=
    Nat.mul_le_mul_right
      (n + 1)
      (reconstructionRuleCandidateEnvelope_le n)
  calc
    reconstructionRuleCandidateEnvelope n * (n + 1)
        ≤ (5 * (n + 1) ^ 4) * (n + 1) := h
    _ = 5 * (n + 1) ^ 5 := by
      ring

/--
Arithmetic form of the manuscript's O(n_K^5) output-size statement.

If the generated production count is bounded by the candidate envelope and
each explicitly stored production has encoding length at most n+1, then the
total output encoding is bounded by the degree-five envelope above.
-/
theorem reconstruction_output_encoding_le
    (n productionCount maxProductionEncoding : Nat)
    (hcount :
      productionCount ≤
        reconstructionRuleCandidateEnvelope n)
    (hencoding :
      maxProductionEncoding ≤ n + 1) :
    productionCount * maxProductionEncoding ≤
      reconstructionOutputEncodingEnvelope n := by
  unfold reconstructionOutputEncodingEnvelope
  exact Nat.mul_le_mul hcount hencoding

/--
Sample-specialized version of the degree-five direct-output bound.
-/
theorem reconstruction_output_encoding_from_sample_le
    (K : Finset (Word α))
    (productionCount maxProductionEncoding : Nat)
    (hcount :
      productionCount ≤
        reconstructionRuleCandidateEnvelope
          (reconstructionSampleNorm K))
    (hencoding :
      maxProductionEncoding ≤
        reconstructionSampleNorm K + 1) :
    productionCount * maxProductionEncoding ≤
      reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm K) :=
  reconstruction_output_encoding_le
    (reconstructionSampleNorm K)
    productionCount maxProductionEncoding
    hcount hencoding

end ReconstructionComplexityCounts

end TCS1
end LeanCfgProject
