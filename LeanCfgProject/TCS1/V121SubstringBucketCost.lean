import LeanCfgProject.TCS1.ReconstructionComplexityCounts
import Mathlib.Tactic

/-!
# TCS #1 v121: the missing cubic bucket-count inequality for Rule (U)

The v116+ substring-indexed batch grammar groups observed factor
occurrences by their surrounding context (u,v) and fixed h-value.
A fixed sample word has at most one internal factor in any such
context, so each bucket has at most |K| entries and the total number
of bucket entries is O(n_K^2). Instead of the old quartic
all-pairs-of-factor-slots envelope, only pairs *within buckets*
need to be generated.

This file verifies the exact arithmetic:
  sum_B |B|^2 <= cap * sum_B |B|,
hence at most n_K^3 rule-(U) candidates and O(n_K^4) literal
encoding size when a rule uses at most n_K units of storage.

The remaining obligations for the full *algorithmic* theorem are
to connect these assumptions to an executable indexed bucket
enumerator with its canonical string identifiers, construction
costs and full output table. Do not cite this counting theorem
alone as the full O(n_K^4) constructor.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section V121BucketCost

variable {B : Type u}

/-- Quadratic pairs in each bucket are linear in its size times a cap. -/
theorem v121_bucket_pair_count_le
    (buckets : Finset B)
    (size : B → Nat)
    (cap total : Nat)
    (hcap : ∀ b ∈ buckets, size b ≤ cap)
    (htotal : (∑ b ∈ buckets, size b) ≤ total) :
    (∑ b ∈ buckets, size b * size b) ≤ cap * total := by
  calc
    (∑ b ∈ buckets, size b * size b)
        ≤ ∑ b ∈ buckets, cap * size b := by
            apply Finset.sum_le_sum
            intro b hb
            exact Nat.mul_le_mul_right _ (hcap b hb)
    _ = cap * (∑ b ∈ buckets, size b) := by
          rw [Finset.mul_sum]
    _ ≤ cap * total :=
          Nat.mul_le_mul_left cap htotal

/-- With n^2 entries and bucket cap n, within-bucket pairs are O(n^3). -/
theorem v121_bucket_pair_count_cubic
    (buckets : Finset B)
    (size : B → Nat)
    (n : Nat)
    (hcap : ∀ b ∈ buckets, size b ≤ n)
    (htotal : (∑ b ∈ buckets, size b) ≤ n * n) :
    (∑ b ∈ buckets, size b * size b) ≤ n ^ 3 := by
  calc
    (∑ b ∈ buckets, size b * size b)
        ≤ n * (n * n) :=
      v121_bucket_pair_count_le buckets size n (n * n)
        hcap htotal
    _ = n ^ 3 := by ring

/-- Writing each pair rule in O(n) symbols gives O(n^4) size. -/
theorem v121_bucket_output_count_quartic
    (buckets : Finset B)
    (size : B → Nat)
    (n : Nat)
    (hcap : ∀ b ∈ buckets, size b ≤ n)
    (htotal : (∑ b ∈ buckets, size b) ≤ n * n) :
    n * (∑ b ∈ buckets, size b * size b) ≤ n ^ 4 := by
  calc
    n * (∑ b ∈ buckets, size b * size b) ≤ n * n ^ 3 :=
      Nat.mul_le_mul_left n
        (v121_bucket_pair_count_cubic buckets size n
          hcap htotal)
    _ = n ^ 4 := by ring

end V121BucketCost

end TCS1
end LeanCfgProject
