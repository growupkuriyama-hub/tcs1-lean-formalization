import LeanCfgProject.TCS1.FixedWindowClassicalSubstitutability

/-!
# TCS #1 v69: the (0,0) endpoint

The current manuscript notes that h_{0,0} separates the empty word from the
nonempty words, but that Definition 2 compares only nonempty internal factors.
Consequently the h_{0,0}-substitutability condition is exactly ordinary
substitutability on nonempty factors, and hence agrees with the (0,0) window
condition.

This file makes that endpoint explicit rather than leaving it only as an
informal consequence of the fixed-window construction.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section ZeroWindowEndpoint

variable {α : Type u}

/-- Ordinary substitutability restricted to the nonempty internal factors
used by FixedHSubstitutable. -/
def NonemptyFactorSubstitutable
    (L : Set (Word α)) : Prop :=
  ∀ ⦃x y : Word α⦄,
    x ≠ [] →
    y ≠ [] →
    HaveSharedContext L x y →
    Distribution L x = Distribution L y

/-- The concrete h_{0,0} typing is constant on nonempty words. -/
theorem fixedWindowMonoidHom_zero_eq_of_nonempty
    [Fintype α]
    {x y : Word α}
    (hx : 0 < x.length)
    (hy : 0 < y.length) :
    (fixedWindowMonoidHom (α := α) 0 0).h x =
      (fixedWindowMonoidHom (α := α) 0 0).h y := by
  exact
    zero_type_eq_of_respectsFixedWindowSummary
      (fixedWindowMonoidHom (α := α) 0 0)
      (fixedWindowMonoidHom_respects (α := α) 0 0)
      hx hy

/-- Yoshinaka's (0,0) condition is exactly ordinary substitutability on
nonempty factors. -/
theorem zeroWindowSubstitutable_iff_nonemptyFactorSubstitutable
    (L : Set (Word α)) :
    FixedWindowSubstitutable 0 0 L ↔
      NonemptyFactorSubstitutable L := by
  constructor
  · intro hwin x y hx hy hshared
    rcases hshared with ⟨x₁, z₁, hsharedX, hsharedY⟩
    apply Set.ext
    intro c
    rcases c with ⟨x₂, z₂⟩
    constructor
    · intro hctxX
      change x₂ ++ y ++ z₂ ∈ L
      have hout :=
        hwin [] [] x y x₁ x₂ z₁ z₂
          (by simp) (by simp)
          (by simpa using hx) (by simpa using hy)
          (by simpa using hsharedX)
          (by simpa using hsharedY)
          (by
            change x₂ ++ x ++ z₂ ∈ L at hctxX
            simpa using hctxX)
      simpa using hout
    · intro hctxY
      change x₂ ++ x ++ z₂ ∈ L
      have hout :=
        hwin [] [] y x x₁ x₂ z₁ z₂
          (by simp) (by simp)
          (by simpa using hy) (by simpa using hx)
          (by simpa using hsharedY)
          (by simpa using hsharedX)
          (by
            change x₂ ++ y ++ z₂ ∈ L at hctxY
            simpa using hctxY)
      simpa using hout
  · intro hsub p q y₁ y₂ x₁ x₂ z₁ z₂
      hp hq hne₁ hne₂ h₁ h₂ h₃
    have hp0 : p = [] := by
      cases p with
      | nil => rfl
      | cons a p =>
          simp at hp
    have hq0 : q = [] := by
      cases q with
      | nil => rfl
      | cons a q =>
          simp at hq
    subst p
    subst q
    have hshared :
        HaveSharedContext L y₁ y₂ := by
      refine ⟨x₁, z₁, ?_, ?_⟩
      · simpa using h₁
      · simpa using h₂
    have hdist :
        Distribution L y₁ = Distribution L y₂ :=
      hsub
        (by simpa using hne₁)
        (by simpa using hne₂)
        hshared
    have hmem₁ :
        (x₂, z₂) ∈ Distribution L y₁ := by
      simpa [Distribution] using h₃
    have hmem₂ :
        (x₂, z₂) ∈ Distribution L y₂ := by
      rw [← hdist]
      exact hmem₁
    simpa [Distribution] using hmem₂

/-- Because h_{0,0} is constant on the nonempty fragment, fixed-h
substitutability for the concrete endpoint is also exactly ordinary
nonempty-factor substitutability. -/
theorem fixedHSubstitutable_zeroWindow_iff_nonemptyFactorSubstitutable
    [Fintype α]
    (L : Set (Word α)) :
    FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) 0 0) L
      ↔
    NonemptyFactorSubstitutable L := by
  constructor
  · intro hfix x y hx hy hshared
    have hxpos : 0 < x.length := by
      cases x with
      | nil => exact (hx rfl).elim
      | cons a xs => simp
    have hypos : 0 < y.length := by
      cases y with
      | nil => exact (hy rfl).elim
      | cons a ys => simp
    exact
      hfix hx hy
        (fixedWindowMonoidHom_zero_eq_of_nonempty
          (α := α) hxpos hypos)
        hshared
  · intro hsub x y hx hy _htype hshared
    exact hsub hx hy hshared

/-- Paper-facing endpoint equivalence: the classical (0,0) window condition
and the concrete h_{0,0} fixed-monoid condition coincide. -/
theorem fixedWindowSubstitutable_zero_iff_fixedHSubstitutable
    [Fintype α]
    (L : Set (Word α)) :
    FixedWindowSubstitutable 0 0 L
      ↔
    FixedHSubstitutable
      (fixedWindowMonoidHom (α := α) 0 0) L := by
  rw [zeroWindowSubstitutable_iff_nonemptyFactorSubstitutable,
      fixedHSubstitutable_zeroWindow_iff_nonemptyFactorSubstitutable]

end ZeroWindowEndpoint

end TCS1
end LeanCfgProject
