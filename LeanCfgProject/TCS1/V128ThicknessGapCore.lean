import Mathlib

/-!
# TCS #1 v128: exponential typed-thickness example, E-branch core

A toy alphabet with `false = a` and `true = c` models exactly the
E_0 -> a; E_(n+1) -> E_n E_n | c branch family in
Proposition `prop:typed-thickness-gap` of the v128 manuscript.

Every E_n has an ordinary one-letter yield. However, conditioning its
yield on *no c* forces every internal doubling and hence a length of 2^n.
A matching all-a derivation exists.

This module certifies the combinatorial E-branch mechanism only.
The full proposition additionally requires the fixed two-element typing,
the complete grammar (S_0,U,D,E_n), successful-tree trim/reachability,
reducedness, O(n) source grammar size, and the typed-thickness interface.
-/

namespace LeanCfgProject
namespace TCS1

/-- `false` encodes a; `true` encodes c. -/
inductive ExponentialBranchYield : Nat → List Bool → Prop
  | base : ExponentialBranchYield 0 [false]
  | duplicate {n : Nat} {u v : List Bool}
      (du : ExponentialBranchYield n u)
      (dv : ExponentialBranchYield n v) :
      ExponentialBranchYield (n + 1) (u ++ v)
  | reset {n : Nat} :
      ExponentialBranchYield (n + 1) [true]

/-- The h_c-unit fibre consists exactly of words containing no c. -/
def ExponentialBranchNoC (w : List Bool) : Prop :=
  true ∉ w

/-- At index n, any h_c-unit E-branch yield has length exactly 2^n. -/
theorem exponentialBranch_noC_length
    {n : Nat} {w : List Bool}
    (d : ExponentialBranchYield n w)
    (hnoc : ExponentialBranchNoC w) :
    w.length = 2 ^ n := by
  induction d with
  | base =>
      simp
  | @duplicate n u v du dv ihU ihV =>
      have hU : ExponentialBranchNoC u := by
        intro hm
        exact hnoc (List.mem_append.mpr (Or.inl hm))
      have hV : ExponentialBranchNoC v := by
        intro hm
        exact hnoc (List.mem_append.mpr (Or.inr hm))
      change (u ++ v).length = 2 ^ (n + 1)
      rw [List.length_append, ihU hU, ihV hV, pow_succ]
      omega
  | reset =>
      exact False.elim (hnoc (by simp))

/-- Every E_n has a one-letter ordinary yield (a at n=0, c afterwards). -/
theorem exponentialBranch_has_short_yield (n : Nat) :
    ∃ w : List Bool, ExponentialBranchYield n w ∧ w.length = 1 := by
  cases n with
  | zero =>
      exact ⟨[false], ExponentialBranchYield.base, rfl⟩
  | succ n =>
      exact ⟨[true], ExponentialBranchYield.reset, rfl⟩

/-- An all-a yield of the required exponential length exists at every index. -/
theorem exponentialBranch_has_noC_witness (n : Nat) :
    ∃ w : List Bool,
      ExponentialBranchYield n w ∧
      ExponentialBranchNoC w ∧
      w.length = 2 ^ n := by
  induction n with
  | zero =>
      refine ⟨[false], ExponentialBranchYield.base, ?_, ?_⟩
      · simp [ExponentialBranchNoC]
      · simp
  | succ n ih =>
      obtain ⟨w, dw, hn, hw⟩ := ih
      refine ⟨w ++ w, ExponentialBranchYield.duplicate dw dw, ?_, ?_⟩
      · intro hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hn hm
        · exact hn hm
      · rw [List.length_append, hw, pow_succ]
        omega

/-- The least length of a no-c yield of E_n is forced to be 2^n. -/
theorem exponentialBranch_noC_lower_bound
    (n : Nat) :
    (∃ w : List Bool,
       ExponentialBranchYield n w ∧
       ExponentialBranchNoC w ∧
       w.length = 2 ^ n) ∧
    (∀ w : List Bool,
      ExponentialBranchYield n w →
      ExponentialBranchNoC w →
      2 ^ n ≤ w.length) := by
  constructor
  · exact exponentialBranch_has_noC_witness n
  · intro w dw hn
    exact le_of_eq (exponentialBranch_noC_length dw hn).symm

end TCS1
end LeanCfgProject
