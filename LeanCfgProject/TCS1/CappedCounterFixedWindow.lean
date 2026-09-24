import LeanCfgProject.TCS1.FixedWindowClassicalSubstitutability

/-!
# TCS #1 v78: capped counter versus fixed windows

This module formalizes the semantic core of the regular-separation theorem
from Section 9.  For a cap rho, the language accepts exactly those counter
runs that stay between 0 and rho; reset clears the counter to zero.

For every rho >= 2 and every fixed window (k,l), we construct two factors
with the same k-prefix and l-suffix.  Both factors are accepted, and one
remains accepted after a short right context while the other overflows.
Hence the capped counter language is not (k,l)-substitutable.

The finite-state / fixed-h positive side is packaged separately.
-/

namespace LeanCfgProject
namespace TCS1
namespace CappedCounter

/-- Counter alphabet: increment, decrement, reset. -/
inductive Symbol where
  | up
  | down
  | reset
  deriving DecidableEq, Fintype, Repr

open Symbol

/-- Deterministic scan with upper cap rho and underflow/overflow rejection. -/
def scan (rho : Nat) : Nat → Word Symbol → Option Nat
  | h, [] => some h
  | h, up :: w =>
      if h < rho then
        scan rho (h + 1) w
      else
        none
  | 0, down :: _ => none
  | h + 1, down :: w =>
      scan rho h w
  | _, reset :: w =>
      scan rho 0 w

/-- Scanner composition across concatenation. -/
theorem scan_append
    (rho h : Nat)
    (u v : Word Symbol) :
    scan rho h (u ++ v) =
      match scan rho h u with
      | none => none
      | some k => scan rho k v := by
  induction u generalizing h with
  | nil =>
      simp [scan]
  | cons s u ih =>
      cases s with
      | up =>
          by_cases hh : h < rho
          · simp [scan, hh, ih]
          · simp [scan, hh]
      | down =>
          cases h with
          | zero =>
              simp [scan]
          | succ h =>
              simpa [scan] using ih (h := h)
      | reset =>
          simpa [scan] using ih (h := 0)

/-- n increments are safe whenever the final height is within the cap. -/
theorem scan_replicate_up_of_le
    {rho h n : Nat}
    (hcap : h + n ≤ rho) :
    scan rho h (List.replicate n up) =
      some (h + n) := by
  induction n generalizing h with
  | zero =>
      simp [scan]
  | succ n ih =>
      rw [List.replicate_succ]
      have hh : h < rho := by omega
      simp only [scan, if_pos hh]
      have hcap' : h + 1 + n ≤ rho := by
        omega
      have hi :=
        ih (h := h + 1) hcap'
      simpa [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hi

/-- Too many increments eventually overflow the cap. -/
theorem scan_replicate_up_of_overflow
    {rho h n : Nat}
    (hle : h ≤ rho)
    (hover : rho < h + n) :
    scan rho h (List.replicate n up) =
      none := by
  induction n generalizing h with
  | zero =>
      omega
  | succ n ih =>
      rw [List.replicate_succ]
      by_cases hh : h < rho
      · simp only [scan, if_pos hh]
        have hle' : h + 1 ≤ rho := by omega
        have hover' : rho < h + 1 + n := by
          omega
        exact ih hle' hover'
      · have heq : h = rho := by omega
        simp [scan, heq]

/-- Any number of leading reset symbols leaves initial height zero. -/
theorem scan_reset_prefix
    (rho k : Nat) :
    scan rho 0 (List.replicate k reset) =
      some 0 := by
  induction k with
  | zero =>
      simp [scan]
  | succ k ih =>
      rw [List.replicate_succ]
      simpa [scan] using ih

/-- Repeated down-up pairs preserve every positive height within the cap. -/
def downUpPairs : Nat → Word Symbol
  | 0 => []
  | n + 1 =>
      down :: up :: downUpPairs n

@[simp] theorem downUpPairs_length
    (n : Nat) :
    (downUpPairs n).length = 2 * n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [downUpPairs, ih]
      omega

theorem scan_downUpPairs
    {rho h n : Nat}
    (hpos : 0 < h)
    (hcap : h ≤ rho) :
    scan rho h (downUpPairs n) =
      some h := by
  induction n generalizing h with
  | zero =>
      simp [downUpPairs, scan]
  | succ n ih =>
      cases h with
      | zero =>
          omega
      | succ h =>
          have hh : h < rho := by omega
          have hpos' : 0 < h + 1 := by omega
          have hcap' : h + 1 ≤ rho := by omega
          simp only [downUpPairs, scan, if_pos hh]
          simpa using
            ih (h := h + 1) hpos' hcap'

/--
Length-l suffix window made of down-up pairs, with one final down when l is
odd.
-/
def suffixWindow
    (l : Nat) :
    Word Symbol :=
  downUpPairs (l / 2) ++
    if l % 2 = 0 then [] else [down]

theorem suffixWindow_length
    (l : Nat) :
    (suffixWindow l).length = l := by
  have hmodlt : l % 2 < 2 :=
    Nat.mod_lt l (by decide)
  have hdiv :
      l % 2 + 2 * (l / 2) = l :=
    Nat.mod_add_div l 2
  by_cases hmod : l % 2 = 0
  · simp [suffixWindow, hmod,
      downUpPairs_length]
    omega
  · have hmod1 : l % 2 = 1 := by
      omega
    simp [suffixWindow, hmod, hmod1,
      downUpPairs_length]
    omega

/--
The suffix window preserves a positive height when l is even and lowers it
by one when l is odd.
-/
theorem scan_suffixWindow
    {rho h l : Nat}
    (hpos : 0 < h)
    (hcap : h ≤ rho) :
    scan rho h (suffixWindow l) =
      some (if l % 2 = 0 then h else h - 1) := by
  unfold suffixWindow
  rw [scan_append]
  have hpairs :=
    scan_downUpPairs
      (rho := rho) (h := h) (n := l / 2)
      hpos hcap
  rw [hpairs]
  simp only
  by_cases hmod : l % 2 = 0
  · simp [hmod, scan]
  · cases h with
    | zero =>
        omega
    | succ h =>
        simp [hmod, scan]

/-- Capped counter language: every prefix stays in the interval [0,rho]. -/
def Language
    (rho : Nat) :
    Set (Word Symbol) :=
  {w | ∃ h : Nat, scan rho 0 w = some h}

@[simp] theorem mem_language_iff
    (rho : Nat)
    (w : Word Symbol) :
    w ∈ Language rho ↔
      ∃ h : Nat, scan rho 0 w = some h := by
  rfl

/--
For rho >= 2, the manuscript's capped-counter language is outside every
fixed-window substitutability class.
-/
theorem not_fixedWindowSubstitutable
    (rho : Nat)
    (hrho : 2 ≤ rho)
    (k l : Nat) :
    ¬ FixedWindowSubstitutable
        k l (Language rho) := by
  intro hwin

  let p : Word Symbol :=
    List.replicate k reset
  let q : Word Symbol :=
    suffixWindow l
  let y₁ : Word Symbol :=
    List.replicate (rho - 1) up
  let y₂ : Word Symbol :=
    List.replicate rho up
  let z₂ : Word Symbol :=
    if l % 2 = 0 then [up] else [up, up]

  have hp : p.length = k := by
    simp [p]
  have hq : q.length = l := by
    simpa [q] using suffixWindow_length l
  have hy₁ne :
      p ++ y₁ ++ q ≠ [] := by
    intro hempty
    have hlen :=
      congrArg List.length hempty
    simp [p, y₁, q] at hlen
    omega
  have hy₂ne :
      p ++ y₂ ++ q ≠ [] := by
    intro hempty
    have hlen :=
      congrArg List.length hempty
    simp [p, y₂, q] at hlen
    omega

  have hpScan :
      scan rho 0 p = some 0 := by
    simpa [p] using scan_reset_prefix rho k
  have hy₁Scan :
      scan rho 0 y₁ =
        some (rho - 1) := by
    have hcap :
        0 + (rho - 1) ≤ rho := by omega
    simpa [y₁] using
      (scan_replicate_up_of_le
        (rho := rho) (h := 0)
        (n := rho - 1) hcap)
  have hy₂Scan :
      scan rho 0 y₂ =
        some rho := by
    have hcap :
        0 + rho ≤ rho := by omega
    simpa [y₂] using
      (scan_replicate_up_of_le
        (rho := rho) (h := 0)
        (n := rho) hcap)

  have hq₁Scan :
      scan rho (rho - 1) q =
        some
          (if l % 2 = 0 then
            rho - 1
          else
            rho - 2) := by
    have hpos :
        0 < rho - 1 := by omega
    have hcap :
        rho - 1 ≤ rho := by omega
    have h :=
      scan_suffixWindow
        (rho := rho) (h := rho - 1)
        (l := l) hpos hcap
    by_cases hmod : l % 2 = 0
    · simpa [q, hmod] using h
    · rw [if_neg hmod]
      rw [if_neg hmod] at h
      have heq :
          rho - 1 - 1 = rho - 2 := by
        omega
      simpa [q, heq] using h

  have hq₂Scan :
      scan rho rho q =
        some
          (if l % 2 = 0 then
            rho
          else
            rho - 1) := by
    have hpos :
        0 < rho := by omega
    have hcap :
        rho ≤ rho := le_rfl
    have h :=
      scan_suffixWindow
        (rho := rho) (h := rho)
        (l := l) hpos hcap
    simpa [q] using h

  have hmem₁ :
      p ++ y₁ ++ q ∈ Language rho := by
    by_cases hmod : l % 2 = 0
    · refine ⟨rho - 1, ?_⟩
      simp [scan_append, hpScan,
        hy₁Scan, hq₁Scan, hmod]
    · refine ⟨rho - 2, ?_⟩
      simp [scan_append, hpScan,
        hy₁Scan, hq₁Scan, hmod]

  have hmem₂ :
      p ++ y₂ ++ q ∈ Language rho := by
    by_cases hmod : l % 2 = 0
    · refine ⟨rho, ?_⟩
      simp [scan_append, hpScan,
        hy₂Scan, hq₂Scan, hmod]
    · refine ⟨rho - 1, ?_⟩
      simp [scan_append, hpScan,
        hy₂Scan, hq₂Scan, hmod]

  have hmem₃ :
      p ++ y₁ ++ q ++ z₂ ∈
        Language rho := by
    by_cases hmod : l % 2 = 0
    · have hz :
          scan rho (rho - 1) [up] =
            some rho := by
        have hcap :
            (rho - 1) + 1 ≤ rho := by
          omega
        have hz' :=
          scan_replicate_up_of_le
            (rho := rho) (h := rho - 1)
            (n := 1) hcap
        have heq :
            rho - 1 + 1 = rho := by
          omega
        simpa [heq] using hz'
      refine ⟨rho, ?_⟩
      simp [scan_append, hpScan,
        hy₁Scan, hq₁Scan, z₂, hmod]
      exact hz
    · have hz :
          scan rho (rho - 2) [up, up] =
            some rho := by
        have hcap :
            (rho - 2) + 2 ≤ rho := by
          omega
        have hz' :=
          scan_replicate_up_of_le
            (rho := rho) (h := rho - 2)
            (n := 2) hcap
        have heq :
            rho - 2 + 2 = rho := by
          omega
        simpa [heq] using hz'
      refine ⟨rho, ?_⟩
      simp [scan_append, hpScan,
        hy₁Scan, hq₁Scan, z₂, hmod]
      exact hz

  have hbad :
      p ++ y₂ ++ q ++ z₂ ∈
        Language rho :=
    hwin p q y₁ y₂
      [] [] [] z₂
      hp hq hy₁ne hy₂ne
      (by simpa using hmem₁)
      (by simpa using hmem₂)
      (by simpa [List.append_assoc] using hmem₃)

  rcases hbad with ⟨hfinal, hscanBad⟩
  by_cases hmod : l % 2 = 0
  · have hover :
        scan rho rho [up] = none := by
      have hle : rho ≤ rho := le_rfl
      have hov : rho < rho + 1 := by omega
      simpa using
        (scan_replicate_up_of_overflow
          (rho := rho) (h := rho)
          (n := 1) hle hov)
    simp [scan_append, hpScan,
      hy₂Scan, hq₂Scan, z₂,
      hmod] at hscanBad
    rw [hover] at hscanBad
    contradiction
  · have hover :
        scan rho (rho - 1) [up, up] =
          none := by
      have hle :
          rho - 1 ≤ rho := by omega
      have hov :
          rho < (rho - 1) + 2 := by omega
      simpa using
        (scan_replicate_up_of_overflow
          (rho := rho) (h := rho - 1)
          (n := 2) hle hov)
    simp [scan_append, hpScan,
      hy₂Scan, hq₂Scan, z₂,
      hmod] at hscanBad
    rw [hover] at hscanBad
    contradiction

end CappedCounter
end TCS1
end LeanCfgProject
