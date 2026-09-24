import LeanCfgProject.TCS1.FiniteMonoidObstructionKernel

/-!
# TCS #1 v78: one-bracket Dyck semantic kernel

This module formalizes the two semantic facts used in Section 9 for the
one-bracket Dyck language D1:

* every Dyck word is contextually neutral, hence syntactically congruent to
  epsilon; and
* the factors b^n a^n form the finite-monoid obstruction family, so D1 is not
  fixed-h substitutable for any finite typing.

We use a deterministic stack-height scanner.  This matches the manuscript's
prefix-balance definition but makes insertion/deletion of a balanced Dyck word
especially transparent.
-/

namespace LeanCfgProject
namespace TCS1

universe u

namespace DyckOne

/-- Two-letter alphabet of the one-bracket Dyck language. -/
inductive Symbol where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

open Symbol

/--
Deterministic height scan.  Letter a pushes; letter b pops, with underflow
reported as none.
-/
def scan : Nat → Word Symbol → Option Nat
  | h, [] => some h
  | h, a :: w => scan (h + 1) w
  | 0, b :: _ => none
  | h + 1, b :: w => scan h w

/-- Scanner composition over concatenation. -/
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
      | a =>
          simp [scan, ih]
      | b =>
          cases h with
          | zero =>
              simp [scan]
          | succ h =>
              simpa [scan] using ih (h := h)

/-- Scanning n opening brackets raises the current height by n. -/
theorem scan_replicate_a
    (h n : Nat) :
    scan h (List.replicate n a) =
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

/-- Scanning at most h closing brackets lowers the height by their count. -/
theorem scan_replicate_b_of_le
    {h n : Nat}
    (hn : n ≤ h) :
    scan h (List.replicate n b) =
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

/-- Too many closing brackets cause underflow. -/
theorem scan_replicate_b_of_lt
    {h n : Nat}
    (hn : h < n) :
    scan h (List.replicate n b) =
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

/--
A successful scan can be shifted upward by any initial height increment.
This is the formal version of "a balanced excursion can be traversed at any
ambient stack height".
-/
theorem scan_height_shift
    {h k : Nat}
    (w : Word Symbol)
    (d : Nat)
    (hw : scan h w = some k) :
    scan (h + d) w = some (k + d) := by
  induction w generalizing h k with
  | nil =>
      simp [scan] at hw ⊢
      omega
  | cons s w ih =>
      cases s with
      | a =>
          simp only [scan] at hw ⊢
          have hs :=
            ih (h := h + 1) (k := k) hw
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs
      | b =>
          cases h with
          | zero =>
              simp [scan] at hw
          | succ h =>
              simp only [scan] at hw
              cases d with
              | zero =>
                  simpa [scan] using hw
              | succ d =>
                  have hs :=
                    ih (h := h) (k := k) hw
                  simp only [scan]
                  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs

/-- The one-bracket Dyck language, via deterministic stack acceptance. -/
def Language : Set (Word Symbol) :=
  {w | scan 0 w = some 0}

@[simp] theorem mem_language_iff
    (w : Word Symbol) :
    w ∈ Language ↔ scan 0 w = some 0 := by
  rfl

@[simp] theorem nil_mem :
    ([] : Word Symbol) ∈ Language := by
  simp [Language, scan]

/-- A Dyck word acts as the identity excursion at every ambient height. -/
theorem scan_dyck_at_height
    {x : Word Symbol}
    (hx : x ∈ Language)
    (h : Nat) :
    scan h x = some h := by
  have hs :=
    scan_height_shift x h hx
  simpa using hs

/--
Inserting or deleting a Dyck word at an arbitrary position preserves Dyck
membership.
-/
theorem insert_neutral
    {x : Word Symbol}
    (hx : x ∈ Language)
    (u v : Word Symbol) :
    u ++ x ++ v ∈ Language ↔
      u ++ v ∈ Language := by
  change
    scan 0 (u ++ x ++ v) = some 0 ↔
      scan 0 (u ++ v) = some 0
  simp only [List.append_assoc, scan_append]
  cases hu : scan 0 u with
  | none =>
      simp [hu]
  | some h =>
      have hxH : scan h x = some h :=
        scan_dyck_at_height hx h
      simp [hu, hxH, scan_append]

/-- Every Dyck word is syntactically congruent to epsilon in D1. -/
theorem member_distribution_eq_nil
    {x : Word Symbol}
    (hx : x ∈ Language) :
    Distribution Language x =
      Distribution Language ([] : Word Symbol) := by
  apply Set.ext
  rintro ⟨u, v⟩
  change
    (u ++ x ++ v ∈ Language) ↔
      (u ++ [] ++ v ∈ Language)
  simpa using insert_neutral hx u v

/-- The bad factor b^n a^n used in the finite-monoid obstruction. -/
def badFactor (n : Nat) : Word Symbol :=
  List.replicate n b ++ List.replicate n a

/--
The manuscript's context calculation:
a^m (b^n a^n) b^m is Dyck exactly when n ≤ m.
-/
theorem context_badFactor_mem_iff
    (m n : Nat) :
    List.replicate m a ++
        badFactor n ++
        List.replicate m b ∈ Language
      ↔
    n ≤ m := by
  change
    scan 0
        (List.replicate m a ++
          (List.replicate n b ++ List.replicate n a) ++
          List.replicate m b) =
      some 0
      ↔
    n ≤ m
  by_cases hnm : n ≤ m
  · have h1 :
        scan 0 (List.replicate m a) =
          some m := by
        simpa using scan_replicate_a 0 m
    have h2 :
        scan m (List.replicate n b) =
          some (m - n) :=
      scan_replicate_b_of_le hnm
    have h3 :
        scan (m - n) (List.replicate n a) =
          some m := by
      rw [scan_replicate_a]
      congr 1
      omega
    have h4 :
        scan m (List.replicate m b) =
          some 0 := by
      simpa using
        scan_replicate_b_of_le (show m ≤ m from le_rfl)
    have hscan :
        scan 0
            (List.replicate m a ++
              (List.replicate n b ++ List.replicate n a) ++
              List.replicate m b) =
          some 0 := by
      simpa [List.append_assoc, scan_append, h1, h2, h3, h4]
    exact ⟨fun _ => hnm, fun _ => hscan⟩
  · have hlt : m < n := by omega
    have h1 :
        scan 0 (List.replicate m a) =
          some m := by
        simpa using scan_replicate_a 0 m
    have h2 :
        scan m (List.replicate n b) =
          none :=
      scan_replicate_b_of_lt hlt
    have hscan :
        scan 0
            (List.replicate m a ++
              (List.replicate n b ++ List.replicate n a) ++
              List.replicate m b) =
          none := by
      simpa [List.append_assoc, scan_append, h1, h2]
    constructor
    · intro hmem
      rw [hscan] at hmem
      contradiction
    · intro hn
      exact False.elim (hnm hn)

/-- Nat-indexed nonempty obstruction family b^(n+1) a^(n+1). -/
def obstructionFactor (n : Nat) : Word Symbol :=
  badFactor (n + 1)

theorem obstructionFactor_ne_nil
    (n : Nat) :
    obstructionFactor n ≠ [] := by
  simp [obstructionFactor, badFactor]

/--
If i < j, the two obstruction factors have a common context but different
full distributions.
-/
theorem obstructionFactor_bad_of_lt
    {i j : Nat}
    (hij : i < j) :
    HaveSharedContext Language
        (obstructionFactor i)
        (obstructionFactor j)
      ∧
    Distribution Language (obstructionFactor i) ≠
      Distribution Language (obstructionFactor j) := by
  let p := i + 1
  let q := j + 1
  have hpq : p < q := by
    dsimp [p, q]
    omega
  have hip :
      List.replicate q a ++
          obstructionFactor i ++
          List.replicate q b ∈ Language := by
    rw [show obstructionFactor i = badFactor p by
      simp [obstructionFactor, p]]
    exact
      (context_badFactor_mem_iff q p).2
        (by omega)
  have hjq :
      List.replicate q a ++
          obstructionFactor j ++
          List.replicate q b ∈ Language := by
    rw [show obstructionFactor j = badFactor q by
      simp [obstructionFactor, q]]
    exact
      (context_badFactor_mem_iff q q).2 le_rfl
  constructor
  · exact
      ⟨List.replicate q a,
        List.replicate q b,
        hip, hjq⟩
  · intro hdist
    have hiSmall :
        (List.replicate p a,
          List.replicate p b) ∈
        Distribution Language
          (obstructionFactor i) := by
      change
        List.replicate p a ++
            obstructionFactor i ++
            List.replicate p b ∈ Language
      rw [show obstructionFactor i = badFactor p by
        simp [obstructionFactor, p]]
      exact
        (context_badFactor_mem_iff p p).2 le_rfl
    have hjSmall :
        (List.replicate p a,
          List.replicate p b) ∈
        Distribution Language
          (obstructionFactor j) := by
      rw [← hdist]
      exact hiSmall
    change
      List.replicate p a ++
          obstructionFactor j ++
          List.replicate p b ∈ Language at hjSmall
    rw [show obstructionFactor j = badFactor q by
      simp [obstructionFactor, q]] at hjSmall
    have :=
      (context_badFactor_mem_iff p q).1 hjSmall
    omega

/--
Distinct obstruction factors have a common Dyck context but different full
distributions.
-/
theorem obstructionFactor_bad
    {i j : Nat}
    (hij : i ≠ j) :
    HaveSharedContext Language
        (obstructionFactor i)
        (obstructionFactor j)
      ∧
    Distribution Language (obstructionFactor i) ≠
      Distribution Language (obstructionFactor j) := by
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

/-- D1 lies outside every fixed finite-monoid substitutability class. -/
theorem not_fixedH
    {M : Type u} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Symbol M) :
    ¬ FixedHSubstitutable H Language := by
  exact
    finiteMonoid_obstruction
      H Language obstructionFactor
      obstructionFactor_ne_nil
      obstructionFactor_bad

end DyckOne

end TCS1
end LeanCfgProject
