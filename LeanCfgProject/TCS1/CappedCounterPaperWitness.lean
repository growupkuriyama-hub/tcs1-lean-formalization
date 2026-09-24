import LeanCfgProject.TCS1.CappedCounterFiniteState
import LeanCfgProject.TCS1.FixedWindowCounterexampleCriterion

/-!
# TCS #1 v78: exact capped-counter witness from the manuscript

Theorem ctr-non-kl in the v78 manuscript uses

  s = (up down)^k up^(rho-1) #^l,
  t = (up down)^k up^rho #^l.

The two words have the same length-k prefix and the same length-l suffix,
both are in CTR_rho, while adding one leading up keeps s accepted and makes t
overflow before the first reset.  This module verifies that exact witness and
then invokes the generic fixed-window counterexample criterion.
-/

namespace LeanCfgProject
namespace TCS1
namespace CappedCounter

open Symbol

/-- The manuscript's alternating prefix (up down)^k. -/
def upDownPairs : Nat → Word Symbol
  | 0 => []
  | n + 1 =>
      up :: down :: upDownPairs n

@[simp] theorem upDownPairs_length
    (n : Nat) :
    (upDownPairs n).length = 2 * n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [upDownPairs, ih]
      omega

/-- Alternating up-down pairs preserve any height strictly below the cap. -/
theorem scan_upDownPairs
    {rho h n : Nat}
    (hcap : h < rho) :
    scan rho h (upDownPairs n) =
      some h := by
  induction n with
  | zero =>
      simp [upDownPairs, scan]
  | succ n ih =>
      simp [upDownPairs, scan, hcap, ih]

/-- A suffix consisting only of resets can never reject. -/
theorem scan_reset_suffix_exists
    (rho h l : Nat) :
    ∃ q : Nat,
      scan rho h
        (List.replicate l reset) =
      some q := by
  induction l generalizing h with
  | zero =>
      exact ⟨h, by simp [scan]⟩
  | succ l ih =>
      rw [List.replicate_succ]
      simp only [scan]
      exact ih (h := 0)

/-- The manuscript's smaller fixed-window witness. -/
def paperS
    (rho k l : Nat) :
    Word Symbol :=
  upDownPairs k ++
    List.replicate (rho - 1) up ++
    List.replicate l reset

/-- The manuscript's larger fixed-window witness. -/
def paperT
    (rho k l : Nat) :
    Word Symbol :=
  upDownPairs k ++
    List.replicate rho up ++
    List.replicate l reset

theorem paperS_mem
    (rho k l : Nat)
    (hrho : 2 ≤ rho) :
    paperS rho k l ∈ Language rho := by
  have hpairs :
      scan rho 0 (upDownPairs k) =
        some 0 :=
    scan_upDownPairs
      (rho := rho) (h := 0) (n := k)
      (by omega)
  have hups :
      scan rho 0
          (List.replicate (rho - 1) up) =
        some (rho - 1) := by
    have hcap :
        0 + (rho - 1) ≤ rho := by
      omega
    simpa using
      (scan_replicate_up_of_le
        (rho := rho) (h := 0)
        (n := rho - 1) hcap)
  rcases
      scan_reset_suffix_exists
        rho (rho - 1) l with
    ⟨q, hreset⟩
  refine ⟨q, ?_⟩
  change
    scan rho 0
      ((upDownPairs k ++
          List.replicate (rho - 1) up) ++
        List.replicate l reset) =
      some q
  simpa [scan_append, hpairs, hups] using hreset

theorem paperT_mem
    (rho k l : Nat)
    (hrho : 2 ≤ rho) :
    paperT rho k l ∈ Language rho := by
  have hpairs :
      scan rho 0 (upDownPairs k) =
        some 0 :=
    scan_upDownPairs
      (rho := rho) (h := 0) (n := k)
      (by omega)
  have hups :
      scan rho 0
          (List.replicate rho up) =
        some rho := by
    have hcap :
        0 + rho ≤ rho := by
      omega
    simpa using
      (scan_replicate_up_of_le
        (rho := rho) (h := 0)
        (n := rho) hcap)
  rcases
      scan_reset_suffix_exists
        rho rho l with
    ⟨q, hreset⟩
  refine ⟨q, ?_⟩
  change
    scan rho 0
      ((upDownPairs k ++
          List.replicate rho up) ++
        List.replicate l reset) =
      some q
  simpa [scan_append, hpairs, hups] using hreset

/-- The distinguishing left context up keeps the smaller witness accepted. -/
theorem up_paperS_mem
    (rho k l : Nat)
    (hrho : 2 ≤ rho) :
    up :: paperS rho k l ∈
      Language rho := by
  have hpairs :
      scan rho 1 (upDownPairs k) =
        some 1 :=
    scan_upDownPairs
      (rho := rho) (h := 1) (n := k)
      (by omega)
  have hups :
      scan rho 1
          (List.replicate (rho - 1) up) =
        some rho := by
    have hcap :
        1 + (rho - 1) ≤ rho := by
      omega
    have h :=
      scan_replicate_up_of_le
        (rho := rho) (h := 1)
        (n := rho - 1) hcap
    have heq :
        1 + (rho - 1) = rho := by
      omega
    simpa [heq] using h
  rcases
      scan_reset_suffix_exists
        rho rho l with
    ⟨q, hreset⟩
  refine ⟨q, ?_⟩
  change
    scan rho 0
      (up ::
        ((upDownPairs k ++
            List.replicate (rho - 1) up) ++
          List.replicate l reset)) =
      some q
  have hzero : 0 < rho := by omega
  simp only [scan, if_pos hzero]
  simpa [scan_append, hpairs, hups] using hreset

/-- The same leading up makes the larger witness overflow before any reset. -/
theorem up_paperT_not_mem
    (rho k l : Nat)
    (hrho : 2 ≤ rho) :
    up :: paperT rho k l ∉
      Language rho := by
  have hpairs :
      scan rho 1 (upDownPairs k) =
        some 1 :=
    scan_upDownPairs
      (rho := rho) (h := 1) (n := k)
      (by omega)
  have hover :
      scan rho 1
          (List.replicate rho up) =
        none := by
    have hle : 1 ≤ rho := by omega
    have hov : rho < 1 + rho := by omega
    exact
      scan_replicate_up_of_overflow
        (rho := rho) (h := 1)
        (n := rho) hle hov
  intro hmem
  rcases hmem with ⟨q, hscan⟩
  change
    scan rho 0
      (up ::
        ((upDownPairs k ++
            List.replicate rho up) ++
          List.replicate l reset)) =
      some q at hscan
  have hzero : 0 < rho := by omega
  simp only [scan, if_pos hzero] at hscan
  simpa [scan_append, hpairs, hover] using hscan

theorem paperS_ne_nil
    (rho k l : Nat)
    (hrho : 2 ≤ rho) :
    paperS rho k l ≠ [] := by
  intro hnil
  have hlen :=
    congrArg List.length hnil
  simp [paperS, upDownPairs_length] at hlen
  omega

theorem paperT_ne_nil
    (rho k l : Nat)
    (hrho : 2 ≤ rho) :
    paperT rho k l ≠ [] := by
  intro hnil
  have hlen :=
    congrArg List.length hnil
  simp [paperT, upDownPairs_length] at hlen
  omega

/--
The two manuscript witnesses have exactly the same tagged fixed-window
summary.
-/
theorem paper_sameFixedWindowSummary
    (rho k l : Nat)
    (hrho : 2 ≤ rho) :
    SameFixedWindowSummary k l
      (paperS rho k l)
      (paperT rho k l) := by
  by_cases hkl : k + l = 0
  · have hk : k = 0 := by omega
    have hl : l = 0 := by omega
    subst k
    subst l
    exact
      zero_words_sameFixedWindowSummary
        (List.length_pos_of_ne_nil
          (paperS_ne_nil rho 0 0 hrho))
        (List.length_pos_of_ne_nil
          (paperT_ne_nil rho 0 0 hrho))
  · have hklpos : 0 < k + l := by omega
    let p : Word Symbol :=
      (upDownPairs k).take k
    let q : Word Symbol :=
      List.replicate l reset
    let m₁ : Word Symbol :=
      (upDownPairs k).drop k ++
        List.replicate (rho - 1) up
    let m₂ : Word Symbol :=
      (upDownPairs k).drop k ++
        List.replicate rho up
    have hp : p.length = k := by
      dsimp [p]
      simp [upDownPairs_length]
      omega
    have hq : q.length = l := by
      simp [q]
    have hpair :
        p ++ (upDownPairs k).drop k =
          upDownPairs k := by
      dsimp [p]
      exact List.take_append_drop k
        (upDownPairs k)
    have hs :
        paperS rho k l =
          p ++ m₁ ++ q := by
      unfold paperS
      rw [← hpair]
      simp [m₁, q, List.append_assoc]
    have ht :
        paperT rho k l =
          p ++ m₂ ++ q := by
      unfold paperT
      rw [← hpair]
      simp [m₂, q, List.append_assoc]
    rw [hs, ht]
    exact
      boundary_words_sameFixedWindowSummary
        hklpos p q m₁ m₂ hp hq

/-- Both paper witnesses share the empty context. -/
theorem paper_shared_context
    (rho k l : Nat)
    (hrho : 2 ≤ rho) :
    HaveSharedContext
      (Language rho)
      (paperS rho k l)
      (paperT rho k l) := by
  exact
    ⟨[], [],
      by simpa using paperS_mem rho k l hrho,
      by simpa using paperT_mem rho k l hrho⟩

/--
Exact Lean counterpart of the proof of Theorem ctr-non-kl in the v78
manuscript.
-/
theorem not_fixedWindowSubstitutable_paperWitness
    (rho : Nat)
    (hrho : 2 ≤ rho)
    (k l : Nat) :
    ¬ FixedWindowSubstitutable
        k l (Language rho) := by
  apply
    not_fixedWindowSubstitutable_of_distinguishing_context
      k l (Language rho)
      (paperS rho k l)
      (paperT rho k l)
      (paperS_ne_nil rho k l hrho)
      (paperT_ne_nil rho k l hrho)
      (paper_sameFixedWindowSummary
        rho k l hrho)
      (paper_shared_context
        rho k l hrho)
      [up] []
  · simpa using
      up_paperS_mem rho k l hrho
  · simpa using
      up_paperT_not_mem rho k l hrho

end CappedCounter
end TCS1
end LeanCfgProject
