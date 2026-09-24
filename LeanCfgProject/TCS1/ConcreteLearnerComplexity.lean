import LeanCfgProject.TCS1.ConcreteConservativeLearner
import LeanCfgProject.TCS1.ReconstructionFiniteCandidateSpaces

/-!
# TCS #1: complexity bookkeeping along the concrete conservative run

The manuscript measures each sequential update against the encoded size of all
positive data seen so far.  The conservative learner stores sets, so repeated
examples disappear from the accumulated sample.  This file verifies the two
basic size invariants needed for the polynomial-update corollary:

* the encoded norm of the accumulated finite sample is at most the encoded
  prefix size of the presented text;
* the finite sample code underlying the current conservative hypothesis is also
  at most that prefix size.

Together with the reconstruction-complexity counting module, every rebuild
therefore has the same explicit degree-five reconstruction-size envelope as a
polynomial in the data prefix seen so far.

The separate CFG-membership algorithm/cost theorem used on keep-vs-rebuild
tests is not formalized here.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ConcreteLearnerComplexity

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]

/-- Encoded size of the positive text prefix through stage n. -/
def positiveDataPrefixNorm
    (datum : Nat → Word α) :
    Nat → Nat
  | 0 => 0
  | n + 1 =>
      positiveDataPrefixNorm datum n +
        ((datum (n + 1)).length + 1)

/-- Inserting one word increases sample norm by at most that word's encoding. -/
theorem reconstructionSampleNorm_insert_le
    (K : Finset (Word α))
    (w : Word α) :
    reconstructionSampleNorm (insert w K) ≤
      reconstructionSampleNorm K + (w.length + 1) := by
  classical
  by_cases hw : w ∈ K
  · simp [reconstructionSampleNorm, hw]
  · simp [reconstructionSampleNorm, hw,
      Nat.add_assoc, Nat.add_comm]

/-- The text-prefix norm is monotone by one stage. -/
theorem positiveDataPrefixNorm_le_succ
    (datum : Nat → Word α)
    (n : Nat) :
    positiveDataPrefixNorm datum n ≤
      positiveDataPrefixNorm datum (n + 1) := by
  simp [positiveDataPrefixNorm]

/--
The accumulated set K_n never has larger encoding than the text prefix from
which it was formed; duplicate positive examples can only make it smaller.
-/
theorem concreteAccumulatedSample_norm_le_prefix
    (datum : Nat → Word α) :
    ∀ n,
      reconstructionSampleNorm
          (concreteAccumulatedSample datum n)
        ≤
      positiveDataPrefixNorm datum n := by
  intro n
  induction n with
  | zero =>
      simp [concreteAccumulatedSample,
        reconstructionSampleNorm,
        positiveDataPrefixNorm]
  | succ n ih =>
      have hins :=
        reconstructionSampleNorm_insert_le
          (concreteAccumulatedSample datum n)
          (datum (n + 1))
      rw [concreteAccumulatedSample_succ]
      rw [positiveDataPrefixNorm]
      exact
        le_trans hins
          (Nat.add_le_add_right ih
            ((datum (n + 1)).length + 1))

/--
The sample code carried by the current conservative hypothesis is also bounded
by the encoded positive-data prefix.
-/
theorem concreteConservativeHypothesis_norm_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) :
    ∀ n,
      reconstructionSampleNorm
          (concreteConservativeHypothesis H datum n)
        ≤
      positiveDataPrefixNorm datum n := by
  intro n
  induction n with
  | zero =>
      simp [concreteConservativeHypothesis,
        reconstructionSampleNorm,
        positiveDataPrefixNorm]
  | succ n ih =>
      classical
      by_cases hgen :
          datum (n + 1) ∈
            BatchLanguage H
              (concreteConservativeHypothesis H datum n)
      · rw [concreteConservativeHypothesis_keep
          H datum n hgen]
        exact
          le_trans ih
            (positiveDataPrefixNorm_le_succ datum n)
      · rw [concreteConservativeHypothesis_rebuild
          H datum n hgen]
        exact
          concreteAccumulatedSample_norm_le_prefix
            datum (n + 1)

/--
The quadratic cache majorant is monotone in the sample-size parameter.
-/
theorem reconstruction_degreeTwo_mono
    {a b : Nat}
    (hab : a ≤ b) :
    (a + 1) ^ 2 ≤ (b + 1) ^ 2 := by
  exact
    Nat.pow_le_pow_left
      (Nat.add_le_add_right hab 1) 2

/--
The quartic candidate-space majorant is monotone in the sample-size parameter.
-/
theorem reconstruction_degreeFour_mono
    {a b : Nat}
    (hab : a ≤ b) :
    5 * (a + 1) ^ 4 ≤
      5 * (b + 1) ^ 4 := by
  apply Nat.mul_le_mul_left
  exact
    Nat.pow_le_pow_left
      (Nat.add_le_add_right hab 1) 4

/--
The actual finite rule-candidate space at stage n is quartically bounded by
the encoded positive-data prefix seen by that stage.
-/
theorem concreteAccumulated_candidateSpace_card_le_prefix_fourth
    (datum : Nat → Word α)
    (n : Nat) :
    Fintype.card
        (ReconstructionRuleCandidateSpace
          (concreteAccumulatedSample datum n))
      ≤
    5 * (positiveDataPrefixNorm datum n + 1) ^ 4 := by
  have hcandidate :
      Fintype.card
          (ReconstructionRuleCandidateSpace
            (concreteAccumulatedSample datum n))
        ≤
      5 *
        (reconstructionSampleNorm
            (concreteAccumulatedSample datum n) + 1) ^ 4 :=
    reconstructionRuleCandidateSpace_card_le_fourth
      (concreteAccumulatedSample datum n)
  have hnorm :
      reconstructionSampleNorm
          (concreteAccumulatedSample datum n)
        ≤
      positiveDataPrefixNorm datum n :=
    concreteAccumulatedSample_norm_le_prefix datum n
  exact
    le_trans hcandidate
      (reconstruction_degreeFour_mono hnorm)

/--
The substring/type cache candidate space is quadratically bounded by the
encoded data prefix.
-/
theorem concreteAccumulated_factorCache_card_le_prefix_sq
    (datum : Nat → Word α)
    (n : Nat) :
    Fintype.card
        (ReconstructionFactorSlot
          (concreteAccumulatedSample datum n))
      ≤
    (positiveDataPrefixNorm datum n + 1) ^ 2 := by
  have hslot :
      Fintype.card
          (ReconstructionFactorSlot
            (concreteAccumulatedSample datum n))
        ≤
      (reconstructionSampleNorm
          (concreteAccumulatedSample datum n)) ^ 2 :=
    reconstructionFactorSlot_card_le_sq
      (concreteAccumulatedSample datum n)
  have hnorm :
      reconstructionSampleNorm
          (concreteAccumulatedSample datum n)
        ≤
      positiveDataPrefixNorm datum n :=
    concreteAccumulatedSample_norm_le_prefix datum n
  have hpow :
      (reconstructionSampleNorm
          (concreteAccumulatedSample datum n)) ^ 2
        ≤
      (positiveDataPrefixNorm datum n + 1) ^ 2 := by
    exact Nat.pow_le_pow_left
      (le_trans hnorm (Nat.le_add_right _ _)) 2
  exact le_trans hslot hpow

/--
Even when every candidate comparison is charged a full linear direct-encoding
cost, scanning the complete finite reconstruction candidate space is bounded
by the same degree-five polynomial in the data prefix.
-/
theorem concreteAccumulated_directCandidateScan_le_prefix_degreeFive
    (datum : Nat → Word α)
    (n : Nat) :
    Fintype.card
        (ReconstructionRuleCandidateSpace
          (concreteAccumulatedSample datum n))
        *
      (positiveDataPrefixNorm datum n + 1)
      ≤
    5 * (positiveDataPrefixNorm datum n + 1) ^ 5 := by
  have hcard :=
    concreteAccumulated_candidateSpace_card_le_prefix_fourth
      datum n
  have hmul :=
    Nat.mul_le_mul_right
      (positiveDataPrefixNorm datum n + 1)
      hcard
  calc
    Fintype.card
        (ReconstructionRuleCandidateSpace
          (concreteAccumulatedSample datum n))
        *
      (positiveDataPrefixNorm datum n + 1)
      ≤
    (5 * (positiveDataPrefixNorm datum n + 1) ^ 4) *
      (positiveDataPrefixNorm datum n + 1) := hmul
    _ =
      5 * (positiveDataPrefixNorm datum n + 1) ^ 5 := by
        ring

/--
The degree-five reconstruction majorant is monotone in the sample-size
parameter.
-/
theorem reconstruction_degreeFive_mono
    {a b : Nat}
    (hab : a ≤ b) :
    5 * (a + 1) ^ 5 ≤
      5 * (b + 1) ^ 5 := by
  apply Nat.mul_le_mul_left
  exact
    Nat.pow_le_pow_left
      (Nat.add_le_add_right hab 1) 5

/--
The next presented word's own encoding is bounded by the encoded prefix after
that word has been read.
-/
theorem nextDatum_encoding_le_prefix
    (datum : Nat → Word α)
    (n : Nat) :
    (datum (n + 1)).length + 1 ≤
      positiveDataPrefixNorm datum (n + 1) := by
  simp [positiveDataPrefixNorm]

/--
The reconstruction-output envelope attached to the accumulated rebuild sample
is degree-five in the encoded data prefix, without introducing auxiliary
production-count parameters.
-/
theorem concreteAccumulated_outputEnvelope_le_prefix_degreeFive
    (datum : Nat → Word α)
    (n : Nat) :
    reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm
          (concreteAccumulatedSample datum n))
      ≤
    5 * (positiveDataPrefixNorm datum n + 1) ^ 5 := by
  have hdeg :
      reconstructionOutputEncodingEnvelope
          (reconstructionSampleNorm
            (concreteAccumulatedSample datum n))
        ≤
      5 *
        (reconstructionSampleNorm
            (concreteAccumulatedSample datum n) + 1) ^ 5 :=
    reconstructionOutputEncodingEnvelope_le_degreeFive
      (reconstructionSampleNorm
        (concreteAccumulatedSample datum n))
  have hnorm :
      reconstructionSampleNorm
          (concreteAccumulatedSample datum n)
        ≤
      positiveDataPrefixNorm datum n :=
    concreteAccumulatedSample_norm_le_prefix datum n
  exact
    le_trans hdeg
      (reconstruction_degreeFive_mono hnorm)

/--
Every current conservative hypothesis has the same degree-five reconstruction
envelope in the data prefix seen so far.  This supplies the grammar-size premise
used by the manuscript's polynomial CFG-membership update argument.
-/
theorem concreteCurrentHypothesis_outputEnvelope_le_prefix_degreeFive
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm
          (concreteConservativeHypothesis H datum n))
      ≤
    5 * (positiveDataPrefixNorm datum n + 1) ^ 5 := by
  have hdeg :
      reconstructionOutputEncodingEnvelope
          (reconstructionSampleNorm
            (concreteConservativeHypothesis H datum n))
        ≤
      5 *
        (reconstructionSampleNorm
            (concreteConservativeHypothesis H datum n) + 1) ^ 5 :=
    reconstructionOutputEncodingEnvelope_le_degreeFive
      (reconstructionSampleNorm
        (concreteConservativeHypothesis H datum n))
  have hnorm :
      reconstructionSampleNorm
          (concreteConservativeHypothesis H datum n)
        ≤
      positiveDataPrefixNorm datum n :=
    concreteConservativeHypothesis_norm_le_prefix
      H datum n
  exact
    le_trans hdeg
      (reconstruction_degreeFive_mono hnorm)

/--
Any rebuild at stage n has the degree-five output-size majorant evaluated at
the encoded data prefix seen by that stage.

The two local parameters are the number of emitted rules and the largest
direct rule encoding.  The assumptions are precisely the counting/encoding
obligations verified by the reconstruction candidate analysis.
-/
theorem concrete_rebuild_output_le_prefix_degreeFive
    (datum : Nat → Word α)
    (n productionCount maxProductionEncoding : Nat)
    (hcount :
      productionCount ≤
        reconstructionRuleCandidateEnvelope
          (reconstructionSampleNorm
            (concreteAccumulatedSample datum n)))
    (hencoding :
      maxProductionEncoding ≤
        reconstructionSampleNorm
          (concreteAccumulatedSample datum n) + 1) :
    productionCount * maxProductionEncoding ≤
      5 * (positiveDataPrefixNorm datum n + 1) ^ 5 := by
  have hout :
      productionCount * maxProductionEncoding ≤
        reconstructionOutputEncodingEnvelope
          (reconstructionSampleNorm
            (concreteAccumulatedSample datum n)) :=
    reconstruction_output_encoding_from_sample_le
      (concreteAccumulatedSample datum n)
      productionCount maxProductionEncoding
      hcount hencoding

  have hdeg :
      reconstructionOutputEncodingEnvelope
          (reconstructionSampleNorm
            (concreteAccumulatedSample datum n))
        ≤
      5 *
        (reconstructionSampleNorm
            (concreteAccumulatedSample datum n) + 1) ^ 5 :=
    reconstructionOutputEncodingEnvelope_le_degreeFive
      (reconstructionSampleNorm
        (concreteAccumulatedSample datum n))

  have hnorm :
      reconstructionSampleNorm
          (concreteAccumulatedSample datum n)
        ≤
      positiveDataPrefixNorm datum n :=
    concreteAccumulatedSample_norm_le_prefix datum n

  exact
    le_trans hout
      (le_trans hdeg
        (reconstruction_degreeFive_mono hnorm))



/--
Paper-facing size certificate for one conservative learner update.

At the step processing datum (n+1), the next word encoding, the current
hypothesis reconstruction envelope, a triggered rebuild envelope, and even a
direct linear-cost scan of every reconstruction candidate are all polynomially
bounded by the encoded positive-data prefix through stage n+1.

The only ingredient of Corollary (poly-update) not represented here is the
standard algorithmic theorem that CFG membership is polynomial in grammar and
input size.
-/
theorem concreteConservative_update_size_certificate
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    (datum (n + 1)).length + 1 ≤
        positiveDataPrefixNorm datum (n + 1)
    ∧
    reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm
          (concreteConservativeHypothesis H datum n))
      ≤
        5 * (positiveDataPrefixNorm datum (n + 1) + 1) ^ 5
    ∧
    reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm
          (concreteAccumulatedSample datum (n + 1)))
      ≤
        5 * (positiveDataPrefixNorm datum (n + 1) + 1) ^ 5
    ∧
    Fintype.card
        (ReconstructionRuleCandidateSpace
          (concreteAccumulatedSample datum (n + 1)))
        *
      (positiveDataPrefixNorm datum (n + 1) + 1)
      ≤
        5 * (positiveDataPrefixNorm datum (n + 1) + 1) ^ 5 := by
  constructor
  · exact nextDatum_encoding_le_prefix datum n
  constructor
  · have hcur :=
      concreteCurrentHypothesis_outputEnvelope_le_prefix_degreeFive
        H datum n
    exact
      le_trans hcur
        (reconstruction_degreeFive_mono
          (positiveDataPrefixNorm_le_succ datum n))
  constructor
  · exact
      concreteAccumulated_outputEnvelope_le_prefix_degreeFive
        datum (n + 1)
  · exact
      concreteAccumulated_directCandidateScan_le_prefix_degreeFive
        datum (n + 1)

end ConcreteLearnerComplexity

end TCS1
end LeanCfgProject
