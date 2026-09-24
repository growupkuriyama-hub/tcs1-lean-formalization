import LeanCfgProject.TCS1.FiniteMonoidObstructionKernel

/-!
# TCS #1 v78: uncapped counter obstruction

This module formalizes the first natural deterministic pushdown example from
Section 9.  The alphabet has increment, decrement, and reset symbols.  The
language consists of exactly those words whose counter never underflows.

For the obstruction family up^(n+1), two different factors share a context
but have different full distributions.  The abstract finite-monoid
obstruction kernel then shows that no fixed finite-monoid typing can make the
uncapped counter language substitutable.
-/

namespace LeanCfgProject
namespace TCS1
namespace UncappedCounter

/-- Counter alphabet: increment, decrement, reset. -/
inductive Symbol where
  | up
  | down
  | reset
  deriving DecidableEq, Fintype, Repr

open Symbol

/--
Deterministic counter scan.  None records underflow; reset clears the
current height to zero.
-/
def scan : Nat → Word Symbol → Option Nat
  | h, [] => some h
  | h, up :: w => scan (h + 1) w
  | 0, down :: _ => none
  | h + 1, down :: w => scan h w
  | _, reset :: w => scan 0 w

/-- Scanner composition across concatenation. -/
theorem scan_append
    (h : Nat)
    (u v : Word Symbol) :
    scan h (u ++ v) =
      match scan h u with
      | none => none
      | some k => scan k v := by
  induction u generalizing h with
  | nil =>
      simp [scan]
  | cons s u ih =>
      cases s with
      | up =>
          simp [scan, ih]
      | down =>
          cases h with
          | zero =>
              simp [scan]
          | succ h =>
              simpa [scan] using ih (h := h)
      | reset =>
          simpa [scan] using ih (h := 0)

/-- n increments raise the current counter by n. -/
theorem scan_replicate_up
    (h n : Nat) :
    scan h (List.replicate n up) =
      some (h + n) := by
  induction n generalizing h with
  | zero =>
      simp [scan]
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [scan]
      rw [ih]
      congr 1
      omega

/-- At most h decrements lower the current counter by their count. -/
theorem scan_replicate_down_of_le
    {h n : Nat}
    (hn : n ≤ h) :
    scan h (List.replicate n down) =
      some (h - n) := by
  induction n generalizing h with
  | zero =>
      simp [scan]
  | succ n ih =>
      cases h with
      | zero =>
          omega
      | succ h =>
          rw [List.replicate_succ]
          simp only [scan]
          have hn' : n ≤ h := by omega
          rw [ih hn']
          congr 1
          omega

/-- More decrements than the current counter height cause underflow. -/
theorem scan_replicate_down_of_lt
    {h n : Nat}
    (hn : h < n) :
    scan h (List.replicate n down) =
      none := by
  induction n generalizing h with
  | zero =>
      omega
  | succ n ih =>
      cases h with
      | zero =>
          rw [List.replicate_succ]
          simp [scan]
      | succ h =>
          rw [List.replicate_succ]
          simp only [scan]
          have hn' : h < n := by omega
          exact ih hn'

/-- The uncapped counter language: exactly the scans with no underflow. -/
def Language : Set (Word Symbol) :=
  {w | ∃ h : Nat, scan 0 w = some h}

@[simp] theorem mem_language_iff
    (w : Word Symbol) :
    w ∈ Language ↔
      ∃ h : Nat, scan 0 w = some h := by
  rfl

/--
The core counter calculation: up^m down^n is accepted exactly when n ≤ m.
-/
theorem up_down_mem_iff
    (m n : Nat) :
    List.replicate m up ++
        List.replicate n down ∈ Language
      ↔
    n ≤ m := by
  constructor
  · intro hw
    rcases hw with ⟨h, hscan⟩
    rw [scan_append] at hscan
    have hup :
        scan 0 (List.replicate m up) =
          some m := by
      simpa using scan_replicate_up 0 m
    rw [hup] at hscan
    simp only at hscan
    by_contra hle
    have hlt : m < n := by omega
    have hdown :
        scan m (List.replicate n down) =
          none :=
      scan_replicate_down_of_lt hlt
    rw [hdown] at hscan
    contradiction
  · intro hnm
    refine ⟨m - n, ?_⟩
    rw [scan_append]
    have hup :
        scan 0 (List.replicate m up) =
          some m := by
      simpa using scan_replicate_up 0 m
    rw [hup]
    exact scan_replicate_down_of_le hnm

/-- Nat-indexed nonempty obstruction family up^(n+1). -/
def obstructionFactor
    (n : Nat) :
    Word Symbol :=
  List.replicate (n + 1) up

theorem obstructionFactor_ne_nil
    (n : Nat) :
    obstructionFactor n ≠ [] := by
  simp [obstructionFactor]

/--
If i < j, the factors up^(i+1) and up^(j+1) have a common context but
different full distributions.
-/
theorem obstructionFactor_bad_of_lt
    {i j : Nat}
    (hij : i < j) :
    HaveSharedContext Language
        (obstructionFactor i)
        (obstructionFactor j)
      ∧
    Distribution Language
        (obstructionFactor i) ≠
      Distribution Language
        (obstructionFactor j) := by
  let p := i + 1
  let q := j + 1
  have hpq : p < q := by
    dsimp [p, q]
    omega
  have hip :
      obstructionFactor i ++
          List.replicate p down ∈ Language := by
    rw [show obstructionFactor i =
      List.replicate p up by
        simp [obstructionFactor, p]]
    exact
      (up_down_mem_iff p p).2 le_rfl
  have hjp :
      obstructionFactor j ++
          List.replicate p down ∈ Language := by
    rw [show obstructionFactor j =
      List.replicate q up by
        simp [obstructionFactor, q]]
    exact
      (up_down_mem_iff q p).2
        (by omega)
  constructor
  · exact
      ⟨[], List.replicate p down,
        by simpa using hip,
        by simpa using hjp⟩
  · intro hdist
    have hjq :
        ([], List.replicate q down) ∈
          Distribution Language
            (obstructionFactor j) := by
      change
        obstructionFactor j ++
            List.replicate q down ∈ Language
      rw [show obstructionFactor j =
        List.replicate q up by
          simp [obstructionFactor, q]]
      exact
        (up_down_mem_iff q q).2 le_rfl
    have hiq :
        ([], List.replicate q down) ∈
          Distribution Language
            (obstructionFactor i) := by
      rw [hdist]
      exact hjq
    change
      obstructionFactor i ++
          List.replicate q down ∈ Language at hiq
    rw [show obstructionFactor i =
      List.replicate p up by
        simp [obstructionFactor, p]] at hiq
    have :=
      (up_down_mem_iff p q).1 hiq
    omega

/-- Distinct obstruction factors always have overlapping unequal distributions. -/
theorem obstructionFactor_bad
    {i j : Nat}
    (hij : i ≠ j) :
    HaveSharedContext Language
        (obstructionFactor i)
        (obstructionFactor j)
      ∧
    Distribution Language
        (obstructionFactor i) ≠
      Distribution Language
        (obstructionFactor j) := by
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact obstructionFactor_bad_of_lt hijlt
  · have hswap :=
      obstructionFactor_bad_of_lt hjilt
    rcases hswap with ⟨hshared, hdist⟩
    constructor
    · rcases hshared with
        ⟨u, v, hjL, hiL⟩
      exact ⟨u, v, hiL, hjL⟩
    · exact fun h => hdist h.symm

/-- Uncapped counter obstruction for an arbitrary fixed finite-monoid typing. -/
theorem not_fixedH
    {M : Type*} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Symbol M) :
    ¬ FixedHSubstitutable H Language := by
  exact
    finiteMonoid_obstruction
      H Language obstructionFactor
      obstructionFactor_ne_nil
      obstructionFactor_bad

end UncappedCounter
end TCS1
end LeanCfgProject
