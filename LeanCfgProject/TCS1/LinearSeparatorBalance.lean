import LeanCfgProject.TCS1.LinearSeparatorBoundaryFactors

/-!
# TCS #1 v78: balance kernel for L_{±,e}

The manuscript uses bal(w)=|w|_a-|w|_b for the identity-typed branch of the
fixed-h proof.  Every separator word has balance zero, so two factors in one
shared context have the same balance.  For nonempty boundary-only factors,
the structural classification then forces literal equality.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

def lpmBalance (w : Word LpmSymbol) : Int :=
  (w.count a : Int) - (w.count b : Int)

@[simp] theorem lpmBalance_nil :
    lpmBalance ([] : Word LpmSymbol) = 0 := by
  simp [lpmBalance]

@[simp] theorem lpmBalance_append
    (u v : Word LpmSymbol) :
    lpmBalance (u ++ v) =
      lpmBalance u + lpmBalance v := by
  simp [lpmBalance, List.count_append]
  omega

@[simp] theorem lpmBalance_replicate_a
    (n : Nat) :
    lpmBalance (List.replicate n a) = (n : Int) := by
  simp [lpmBalance, List.count_replicate]

@[simp] theorem lpmBalance_replicate_b
    (n : Nat) :
    lpmBalance (List.replicate n b) = -(n : Int) := by
  simp [lpmBalance, List.count_replicate]

/-- Every word of L_{±,e} has zero a/b balance. -/
theorem lpmBalance_mem_zero
    {w : Word LpmSymbol}
    (hw : w ∈ LpmLanguage) :
    lpmBalance w = 0 := by
  rcases hw with ⟨n, z, rfl, hacc⟩
  cases z <;>
    simp_all [lpmCore, lpmBalance, LpmAccepted,
      List.count_replicate, List.count_append]

/-- Shared occurrence in L_{±,e} forces equal factor balance. -/
theorem lpmBalance_eq_of_sharedContext
    {x y : Word LpmSymbol}
    (hshared :
      HaveSharedContext LpmLanguage x y) :
    lpmBalance x = lpmBalance y := by
  rcases hshared with ⟨u, v, hxL, hyL⟩
  have hx0 := lpmBalance_mem_zero hxL
  have hy0 := lpmBalance_mem_zero hyL
  simp only [lpmBalance_append] at hx0 hy0
  omega

/--
The identity-type branch of the fixed-h proof:
nonempty boundary-only factors sharing a context are literally equal.
-/
theorem lpm_boundary_factors_eq
    {x y : Word LpmSymbol}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hxb :
      ∀ t ∈ x, LpmBoundaryLetter t)
    (hyb :
      ∀ t ∈ y, LpmBoundaryLetter t)
    (hshared :
      HaveSharedContext LpmLanguage x y) :
    x = y := by
  rcases hshared with ⟨u, v, hxL, hyL⟩
  have hbal :
      lpmBalance x = lpmBalance y :=
    lpmBalance_eq_of_sharedContext
      ⟨u, v, hxL, hyL⟩
  rcases lpm_boundary_factor_shape hxne hxb hxL with
      ⟨m, hmpos, hxa⟩ | ⟨m, hmpos, hxbpow⟩ <;>
    rcases lpm_boundary_factor_shape hyne hyb hyL with
      ⟨n, hnpos, hya⟩ | ⟨n, hnpos, hybpow⟩
  · rw [hxa, hya] at hbal ⊢
    simp at hbal
    have hmn : m = n := by omega
    subst n
    rfl
  · rw [hxa, hybpow] at hbal
    simp at hbal
    omega
  · rw [hxbpow, hya] at hbal
    simp at hbal
    omega
  · rw [hxbpow, hybpow] at hbal ⊢
    simp at hbal
    have hmn : m = n := by omega
    subst n
    rfl

end TCS1
end LeanCfgProject
