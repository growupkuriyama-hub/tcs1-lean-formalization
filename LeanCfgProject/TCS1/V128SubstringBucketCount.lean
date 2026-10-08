import LeanCfgProject.TCS1.V128FiniteSubstringGrammar
import LeanCfgProject.TCS1.ReconstructionFiniteCandidateSpaces
import Mathlib.Tactic

/-!
# TCS #1 v128: context-bucket accounting for v116 unary rules

The sharper O(n_K^4) output bound in the v128 manuscript uses
O(n_K^3) unary candidates (U), *not* the generic O(n_K^4)
pair-of-factor-slots envelope of the earlier occurrence grammar.

For each fixed context (p,q) and fixed h-type μ, the bucket consists
of unique observed nonempty factors x such that p x q is a sample.
There is at most ONE factor for each given sample word, so every bucket
has at most |K| elements.

Consequently, for any finite collection of bucket keys, if their
aggregate membership count is at most the two-cut occurrence budget
O(n_K^2), then the emitted ordered-pair count is <= n_K^3.

The required final bridge still to be proved is that the *actual*
bucket-key enumeration contains every v116 unary rule and has
aggregate membership count bounded by the observed occurrence slots.
This module does not yet certify the unconditional v116 O(n_K^4)
output bound or effective runtime of the bucket implementation.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ContextBuckets

variable {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M] [Fintype M]

noncomputable instance observedSubstringLocalFintype
    (K : Finset (Word α)) :
    Fintype (ObservedSubstringNonterminal K) :=
  observedSubstringFintype K

/-- Every item in a given unary-rule bucket is a distinct sample factor
    with exactly the chosen context and h-type. -/
abbrev SubstringContextBucket
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (p q : Word α) (μ : M) :=
  {A : ObservedSubstringNonterminal K //
    Observed K A.1 p q ∧ H.h A.1 = μ}

/-- Associate each bucket factor with its containing sample word. -/
def substringContextBucketSample
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (p q : Word α) (μ : M)
    (A : SubstringContextBucket H K p q μ) :
    ReconstructionSampleWord K :=
  ⟨p ++ A.1.1 ++ q, A.2.1.2⟩

/-- Two factors in one bucket cannot arise from the same sample word. -/
theorem substringContextBucketSample_injective
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (p q : Word α) (μ : M) :
    Function.Injective
      (substringContextBucketSample H K p q μ) := by
  intro A B heq
  have hw : p ++ A.1.1 ++ q = p ++ B.1.1 ++ q :=
    congrArg Subtype.val heq
  have hafter : A.1.1 ++ q = B.1.1 ++ q :=
    List.append_cancel_left hw
  have hfactor : A.1.1 = B.1.1 :=
    List.append_cancel_right hafter
  apply Subtype.ext
  apply Subtype.ext
  exact hfactor

/-- Every context/type bucket has size at most the number of samples. -/
theorem substringContextBucket_card_le_sample_card
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (p q : Word α) (μ : M) :
    Fintype.card (SubstringContextBucket H K p q μ) ≤ K.card := by
  classical
  calc
    Fintype.card (SubstringContextBucket H K p q μ) ≤
      Fintype.card (ReconstructionSampleWord K) :=
      Fintype.card_le_of_injective
        (substringContextBucketSample H K p q μ)
        (substringContextBucketSample_injective H K p q μ)
    _ = K.card := reconstructionSampleWord_card_eq K

/-- The manuscript's decisive sum-of-squares estimate: when bucket entries
    are covered by two-cut sample occurrences, emitting all ordered
    same-bucket pairs costs at most cubically many rule candidates. -/
theorem substringContextBucket_pairCount_le_cube
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (B : Finset ((Word α × Word α) × M))
    (hentries :
      (∑ b ∈ B,
        Fintype.card
          (SubstringContextBucket H K b.1.1 b.1.2 b.2)) ≤
        reconstructionFactorSlotCount K) :
    (∑ b ∈ B,
      (Fintype.card
        (SubstringContextBucket H K b.1.1 b.1.2 b.2)) ^ 2) ≤
      (reconstructionSampleNorm K) ^ 3 := by
  classical
  let s : ((Word α × Word α) × M) → Nat :=
    fun b => Fintype.card
      (SubstringContextBucket H K b.1.1 b.1.2 b.2)
  have hsum : (∑ b ∈ B, (s b) ^ 2) ≤
      K.card * (∑ b ∈ B, s b) := by
    calc
      (∑ b ∈ B, (s b) ^ 2) ≤
          ∑ b ∈ B, K.card * s b := by
        apply Finset.sum_le_sum
        intro b hb
        have hc : s b ≤ K.card :=
          substringContextBucket_card_le_sample_card
            H K b.1.1 b.1.2 b.2
        simpa only [pow_two] using
          (Nat.mul_le_mul_right (s b) hc)
      _ = K.card * (∑ b ∈ B, s b) := by
        rw [Finset.mul_sum]
  calc
    (∑ b ∈ B, (s b) ^ 2) ≤
        K.card * (∑ b ∈ B, s b) := hsum
    _ ≤ reconstructionSampleNorm K *
          reconstructionFactorSlotCount K :=
      Nat.mul_le_mul (reconstructionSample_card_le_norm K)
        hentries
    _ ≤ reconstructionSampleNorm K *
          (reconstructionSampleNorm K) ^ 2 :=
      Nat.mul_le_mul_left _ (reconstructionFactorSlotCount_le_sq K)
    _ = (reconstructionSampleNorm K) ^ 3 := by ring

end ContextBuckets

end TCS1
end LeanCfgProject
