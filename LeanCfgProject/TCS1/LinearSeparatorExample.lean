import LeanCfgProject.TCS1.FixedWindowClassicalSubstitutability

/-!
# TCS #1 v77: the linear separator language L_{±,e}

This module formalizes the concrete language introduced in Section 8.1 of
the v77 manuscript:

  {a^(2m) c b^(2m)} ∪ {a^(2m+1) d b^(2m+1)} ∪ {a^n e b^n}.

The first layer packages its exact membership test and proves the two
negative separation statements from Proposition 8.6:

* it is not Clark--Eyraud substitutable;
* for every fixed k,l it is not (k,l)-substitutable.

The fixed-h positive direction is added in the next layer.
-/

namespace LeanCfgProject
namespace TCS1

inductive LpmSymbol where
  | a | b | c | d | e
  deriving DecidableEq, Fintype, Repr

open LpmSymbol

/-- The balanced word a^n z b^n with center z. -/
def lpmCore (n : Nat) (z : LpmSymbol) : Word LpmSymbol :=
  List.replicate n a ++ [z] ++ List.replicate n b

/-- The center/parity membership condition of equation (8.2). -/
def LpmAccepted (n : Nat) : LpmSymbol → Prop
  | e => True
  | c => n % 2 = 0
  | d => n % 2 = 1
  | a => False
  | b => False

/-- The v77 separator language L_{±,e}. -/
def LpmLanguage : Set (Word LpmSymbol) :=
  { w | ∃ n z, w = lpmCore n z ∧ LpmAccepted n z }

theorem lpmCore_eq_iff
    {n m : Nat} {z z' : LpmSymbol} :
    lpmCore n z = lpmCore m z' ↔
      n = m ∧ z = z' := by
  constructor
  · intro h
    have hlen := congrArg List.length h
    have hnm : n = m := by
      simp [lpmCore] at hlen
      omega
    subst m
    have hfront :
        List.replicate n a ++
            ([z] ++ List.replicate n b) =
          List.replicate n a ++
            ([z'] ++ List.replicate n b) := by
      simpa [lpmCore, List.append_assoc] using h
    have htail :
        [z] ++ List.replicate n b =
          [z'] ++ List.replicate n b :=
      List.append_cancel_left hfront
    have hcenter : [z] = [z'] :=
      List.append_cancel_right htail
    have hzz : z = z' := by
      simpa using hcenter
    exact ⟨rfl, hzz⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Exact membership of a canonical one-center word. -/
theorem lpmCore_mem_iff
    (n : Nat) (z : LpmSymbol) :
    lpmCore n z ∈ LpmLanguage ↔
      LpmAccepted n z := by
  constructor
  · rintro ⟨m, z', hword, hacc⟩
    have hnmz :
        n = m ∧ z = z' :=
      lpmCore_eq_iff.mp hword
    rcases hnmz with ⟨rfl, rfl⟩
    exact hacc
  · intro hacc
    exact ⟨n, z, rfl, hacc⟩

theorem lpm_e_mem (n : Nat) :
    lpmCore n e ∈ LpmLanguage := by
  exact (lpmCore_mem_iff n e).2 trivial

theorem lpm_c_mem_of_even
    {n : Nat} (h : n % 2 = 0) :
    lpmCore n c ∈ LpmLanguage := by
  exact (lpmCore_mem_iff n c).2 h

theorem lpm_d_mem_of_odd
    {n : Nat} (h : n % 2 = 1) :
    lpmCore n d ∈ LpmLanguage := by
  exact (lpmCore_mem_iff n d).2 h

/-- Clark--Eyraud substitutability under the paper's nonempty-factor convention. -/
def ClarkEyraudSubstitutable
    (L : Set (Word LpmSymbol)) : Prop :=
  ∀ ⦃x y : Word LpmSymbol⦄,
    x ≠ [] →
    y ≠ [] →
    HaveSharedContext L x y →
    Distribution L x = Distribution L y

/--
The c/e witness from Proposition 8.6:
c and e share the empty context, but the context (a,b) distinguishes them.
-/
theorem lpm_not_clarkEyraud :
    ¬ ClarkEyraudSubstitutable LpmLanguage := by
  intro hce
  have hshared :
      HaveSharedContext LpmLanguage [c] [e] := by
    refine ⟨[], [], ?_, ?_⟩
    · simpa [lpmCore] using lpm_c_mem_of_even (n := 0) (by simp)
    · simpa [lpmCore] using lpm_e_mem 0
  have hdist :
      Distribution LpmLanguage [c] =
        Distribution LpmLanguage [e] :=
    hce (by simp) (by simp) hshared
  have hectx :
      ([a], [b]) ∈ Distribution LpmLanguage [e] := by
    change [a] ++ [e] ++ [b] ∈ LpmLanguage
    simpa [lpmCore] using lpm_e_mem 1
  have hcctx :
      ([a], [b]) ∈ Distribution LpmLanguage [c] := by
    rw [hdist]
    exact hectx
  have hcmem :
      lpmCore 1 c ∈ LpmLanguage := by
    simpa [Distribution, lpmCore] using hcctx
  have hacc :=
    (lpmCore_mem_iff 1 c).1 hcmem
  simp [LpmAccepted] at hacc

private theorem replicate_sub_add
    (s : LpmSymbol)
    {k r : Nat}
    (hkr : k ≤ r) :
    List.replicate (r - k) s ++
        List.replicate k s =
      List.replicate r s := by
  rw [← List.replicate_add]
  congr
  omega

private theorem replicate_add_sub
    (s : LpmSymbol)
    {k r : Nat}
    (hkr : k ≤ r) :
    List.replicate k s ++
        List.replicate (r - k) s =
      List.replicate r s := by
  rw [← List.replicate_add]
  congr
  omega

/--
For every fixed window (k,l), the manuscript's r_* witness violates
(k,l)-substitutability.
-/
theorem lpm_not_fixedWindowSubstitutable
    (k l : Nat) :
    ¬ FixedWindowSubstitutable k l LpmLanguage := by
  intro hwin
  let r : Nat := 2 * (max k l + 1)
  have hkmax : k ≤ max k l :=
    Nat.le_max_left _ _
  have hlmax : l ≤ max k l :=
    Nat.le_max_right _ _
  have hk : k ≤ r := by
    dsimp [r]
    omega
  have hl : l ≤ r := by
    dsimp [r]
    omega
  have hk1 : k ≤ r + 1 := le_trans hk (Nat.le_succ r)
  have hl1 : l ≤ r + 1 := le_trans hl (Nat.le_succ r)
  have hreven : r % 2 = 0 := by
    simp [r, Nat.mul_mod]
  have hrodd : (r + 1) % 2 = 1 := by
    simp [r, Nat.add_mod, Nat.mul_mod]

  let p : Word LpmSymbol := List.replicate k a
  let q : Word LpmSymbol := List.replicate l b
  let y₁ : Word LpmSymbol := [e]
  let y₂ : Word LpmSymbol := [c]
  let x₁ : Word LpmSymbol := List.replicate (r - k) a
  let z₁ : Word LpmSymbol := List.replicate (r - l) b
  let x₂ : Word LpmSymbol := List.replicate (r + 1 - k) a
  let z₂ : Word LpmSymbol := List.replicate (r + 1 - l) b

  have hp : p.length = k := by simp [p]
  have hq : q.length = l := by simp [q]
  have hy₁ne : p ++ y₁ ++ q ≠ [] := by
    simp [p, q, y₁]
  have hy₂ne : p ++ y₂ ++ q ≠ [] := by
    simp [p, q, y₂]

  have ha₁ :
      x₁ ++ p = List.replicate r a := by
    simpa [x₁, p] using
      (replicate_sub_add a hk)
  have hb₁ :
      q ++ z₁ = List.replicate r b := by
    simpa [q, z₁] using
      (replicate_add_sub b hl)
  have ha₂ :
      x₂ ++ p = List.replicate (r + 1) a := by
    simpa [x₂, p] using
      (replicate_sub_add a hk1)
  have hb₂ :
      q ++ z₂ = List.replicate (r + 1) b := by
    simpa [q, z₂] using
      (replicate_add_sub b hl1)

  have heq₁ :
      x₁ ++ (p ++ y₁ ++ q) ++ z₁ =
        lpmCore r e := by
    calc
      x₁ ++ (p ++ y₁ ++ q) ++ z₁ =
          (x₁ ++ p) ++ y₁ ++ (q ++ z₁) := by
            simp [List.append_assoc]
      _ = lpmCore r e := by
        rw [ha₁, hb₁]
        rfl
  have heq₂ :
      x₁ ++ (p ++ y₂ ++ q) ++ z₁ =
        lpmCore r c := by
    calc
      x₁ ++ (p ++ y₂ ++ q) ++ z₁ =
          (x₁ ++ p) ++ y₂ ++ (q ++ z₁) := by
            simp [List.append_assoc]
      _ = lpmCore r c := by
        rw [ha₁, hb₁]
        rfl
  have heq₃ :
      x₂ ++ (p ++ y₁ ++ q) ++ z₂ =
        lpmCore (r + 1) e := by
    calc
      x₂ ++ (p ++ y₁ ++ q) ++ z₂ =
          (x₂ ++ p) ++ y₁ ++ (q ++ z₂) := by
            simp [List.append_assoc]
      _ = lpmCore (r + 1) e := by
        rw [ha₂, hb₂]
        rfl
  have heq₄ :
      x₂ ++ (p ++ y₂ ++ q) ++ z₂ =
        lpmCore (r + 1) c := by
    calc
      x₂ ++ (p ++ y₂ ++ q) ++ z₂ =
          (x₂ ++ p) ++ y₂ ++ (q ++ z₂) := by
            simp [List.append_assoc]
      _ = lpmCore (r + 1) c := by
        rw [ha₂, hb₂]
        rfl

  have hmem₁ :
      x₁ ++ (p ++ y₁ ++ q) ++ z₁ ∈
        LpmLanguage := by
    rw [heq₁]
    exact lpm_e_mem r
  have hmem₂ :
      x₁ ++ (p ++ y₂ ++ q) ++ z₁ ∈
        LpmLanguage := by
    rw [heq₂]
    exact lpm_c_mem_of_even hreven
  have hmem₃ :
      x₂ ++ (p ++ y₁ ++ q) ++ z₂ ∈
        LpmLanguage := by
    rw [heq₃]
    exact lpm_e_mem (r + 1)

  have hbad :
      x₂ ++ (p ++ y₂ ++ q) ++ z₂ ∈
        LpmLanguage :=
    hwin p q y₁ y₂ x₁ x₂ z₁ z₂
      hp hq hy₁ne hy₂ne hmem₁ hmem₂ hmem₃
  rw [heq₄] at hbad
  have hacc :=
    (lpmCore_mem_iff (r + 1) c).1 hbad
  simp [LpmAccepted, hrodd] at hacc

end TCS1
end LeanCfgProject
