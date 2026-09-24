import LeanCfgProject.TCS1.FixedWindowConcreteMonoid

/-!
# TCS #1 v68: Yoshinaka fixed-window substitutability bridge

This module formalizes the classical (k,l)-substitutability premise used in
Proposition 3.2 and proves that it implies substitutability for the concrete
finite-monoid homomorphism h_{k,l}.

The proof follows the manuscript literally: equality of h_{k,l}-types either
identifies a short word exactly, or supplies a common length-k prefix and
length-l suffix. In the long case, the shared context and an arbitrary
context are fed into the classical three-positive-premise substitution rule.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section FixedWindowClassicalSubstitutability

variable {α : Type u}

/--
Yoshinaka's (k,l)-substitutability condition, with the window variables named
p and q as in the manuscript.

The two compared internal factors are required to be nonempty, matching the
nonempty-fragment convention used by FixedHSubstitutable.
-/
def FixedWindowSubstitutable
    (k l : Nat)
    (L : Set (Word α)) : Prop :=
  ∀ (p q y₁ y₂ x₁ x₂ z₁ z₂ : Word α),
    p.length = k →
    q.length = l →
    p ++ y₁ ++ q ≠ [] →
    p ++ y₂ ++ q ≠ [] →
    x₁ ++ (p ++ y₁ ++ q) ++ z₁ ∈ L →
    x₁ ++ (p ++ y₂ ++ q) ++ z₁ ∈ L →
    x₂ ++ (p ++ y₁ ++ q) ++ z₂ ∈ L →
    x₂ ++ (p ++ y₂ ++ q) ++ z₂ ∈ L

/--
Proposition 3.2, semantic half:
every fixed-window substitutable language is substitutable for the concrete
finite-monoid typing h_{k,l}.
-/
theorem fixedHSubstitutable_of_fixedWindowSubstitutable
    [Fintype α]
    (k l : Nat)
    (L : Set (Word α))
    (hwin : FixedWindowSubstitutable k l L) :
    FixedHSubstitutable
      (fixedWindowMonoidHom (α := α) k l)
      L := by
  intro x y hxne hyne htype hshared
  have hraw :
      fixedWindowRawSummary k l x =
        fixedWindowRawSummary k l y := by
    exact congrArg Subtype.val htype
  have hsame :
      SameFixedWindowSummary k l x y :=
    sameFixedWindowSummary_of_rawSummary_eq
      (α := α) hraw
  rcases hsame with hshort | hlong
  · rcases hshort with ⟨_hxshort, hyx⟩
    subst y
    rfl
  · rcases hlong with
      ⟨_hxcut, _hycut, p, q, y₁, y₂,
        hp, hq, hxword, hyword⟩
    rcases hshared with
      ⟨x₀, z₀, hsharedX, hsharedY⟩
    apply Set.ext
    intro c
    rcases c with ⟨x₂, z₂⟩
    constructor
    · intro hctxX
      have hw₁ne :
          p ++ y₁ ++ q ≠ [] := by
        intro hempty
        apply hxne
        rw [hxword, hempty]
      have hw₂ne :
          p ++ y₂ ++ q ≠ [] := by
        intro hempty
        apply hyne
        rw [hyword, hempty]
      have h₁ :
          x₀ ++ (p ++ y₁ ++ q) ++ z₀ ∈ L := by
        simpa [hxword] using hsharedX
      have h₂ :
          x₀ ++ (p ++ y₂ ++ q) ++ z₀ ∈ L := by
        simpa [hyword] using hsharedY
      have h₃ :
          x₂ ++ (p ++ y₁ ++ q) ++ z₂ ∈ L := by
        change x₂ ++ x ++ z₂ ∈ L at hctxX
        simpa [hxword] using hctxX
      have hout :=
        hwin p q y₁ y₂ x₀ x₂ z₀ z₂
          hp hq hw₁ne hw₂ne h₁ h₂ h₃
      change x₂ ++ y ++ z₂ ∈ L
      simpa [hyword] using hout
    · intro hctxY
      have hw₁ne :
          p ++ y₂ ++ q ≠ [] := by
        intro hempty
        apply hyne
        rw [hyword, hempty]
      have hw₂ne :
          p ++ y₁ ++ q ≠ [] := by
        intro hempty
        apply hxne
        rw [hxword, hempty]
      have h₁ :
          x₀ ++ (p ++ y₂ ++ q) ++ z₀ ∈ L := by
        simpa [hyword] using hsharedY
      have h₂ :
          x₀ ++ (p ++ y₁ ++ q) ++ z₀ ∈ L := by
        simpa [hxword] using hsharedX
      have h₃ :
          x₂ ++ (p ++ y₂ ++ q) ++ z₂ ∈ L := by
        change x₂ ++ y ++ z₂ ∈ L at hctxY
        simpa [hyword] using hctxY
      have hout :=
        hwin p q y₂ y₁ x₀ x₂ z₀ z₂
          hp hq hw₁ne hw₂ne h₁ h₂ h₃
      change x₂ ++ x ++ z₂ ∈ L
      simpa [hxword] using hout

end FixedWindowClassicalSubstitutability

end TCS1
end LeanCfgProject
