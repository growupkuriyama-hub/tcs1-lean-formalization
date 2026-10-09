import LeanCfgProject.TCS1.FixedWindowExactEquivalence
import LeanCfgProject.TCS1.FixedHTypingRefinement

/-!
# TCS #1 v128: positive-word fixed-window kernel reduction

This is a new mathematical bridge for Proposition prop:li-window.
It characterizes a positive-word kernel inclusion by an entirely explicit
boundary-word invariance condition. The boundary statements use the existing
concrete h_{k,l} and the *nonempty-factor* convention of fixed-h substitutability.

Neither direction presumes the locally trivial positive-image semigroup
criterion. The independent finite-semigroup implication remains a later step.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section PositiveWindowKernel

variable {α : Type u} {M : Type v}
variable [Fintype α] [Monoid M] [Fintype M]

/-- Exactly the v128 positive-word kernel inclusion
    ker(h_{k,l})|Sigma+ subset ker(H)|Sigma+. -/
def PositiveWindowKernelRefines
    (H : FixedFiniteMonoidHom α M) (k l : Nat) : Prop :=
  ∀ x y : Word α,
    x ≠ [] → y ≠ [] →
    (fixedWindowMonoidHom (α := α) k l).h x =
      (fixedWindowMonoidHom (α := α) k l).h y →
    H.h x = H.h y

/-- Alternative positive-word form: arbitrary middle substrings become
    indistinguishable after the same length-k prefix and length-l suffix.
    Both entire compared factors must be nonempty (not merely the middle). -/
def PositiveWindowBoundaryInvariant
    (H : FixedFiniteMonoidHom α M) (k l : Nat) : Prop :=
  ∀ p q m₁ m₂ : Word α,
    p.length = k → q.length = l →
    p ++ m₁ ++ q ≠ [] →
    p ++ m₂ ++ q ≠ [] →
    H.h (p ++ m₁ ++ q) = H.h (p ++ m₂ ++ q)

/-- Every positive-word kernel refinement satisfies the explicit boundary law. -/
theorem positiveWindowKernel_refines_implies_boundary
    (H : FixedFiniteMonoidHom α M) (k l : Nat)
    (href : PositiveWindowKernelRefines H k l) :
    PositiveWindowBoundaryInvariant H k l := by
  intro p q m₁ m₂ hp hq hx hy
  have hcutx :
      fixedWindowThreshold k l ≤ (p ++ m₁ ++ q).length := by
    have hxpos : 0 < p.length + m₁.length + q.length := by
      simpa only [List.length_append] using
        (List.length_pos_of_ne_nil hx)
    simp only [List.length_append]
    unfold fixedWindowThreshold
    omega
  have hcuty :
      fixedWindowThreshold k l ≤ (p ++ m₂ ++ q).length := by
    have hypos : 0 < p.length + m₂.length + q.length := by
      simpa only [List.length_append] using
        (List.length_pos_of_ne_nil hy)
    simp only [List.length_append]
    unfold fixedWindowThreshold
    omega
  have hsame :
      SameFixedWindowSummary k l
        (p ++ m₁ ++ q) (p ++ m₂ ++ q) :=
    Or.inr ⟨hcutx, hcuty, p, q, m₁, m₂, hp, hq, rfl, rfl⟩
  exact href (p ++ m₁ ++ q) (p ++ m₂ ++ q)
    hx hy (fixedWindowMonoidHom_respects (α := α) k l _ _ hsame)

/-- Boundary invariance is sufficient for the whole positive-word kernel
    refinement, including (0,0) and the short/long tag. -/
theorem positiveWindowBoundary_implies_kernel_refines
    (H : FixedFiniteMonoidHom α M) (k l : Nat)
    (hboundary : PositiveWindowBoundaryInvariant H k l) :
    PositiveWindowKernelRefines H k l := by
  intro x y hx hy hwin
  have hsame :
      SameFixedWindowSummary k l x y :=
    fixedWindowMonoidHom_reflects (α := α) k l x y hwin
  rcases hsame with ⟨_hshort, hyx⟩ |
    ⟨_hcutx, _hcuty, p, q, m₁, m₂, hp, hq, hxdecomp, hydecomp⟩
  · rw [hyx]
  · rw [hxdecomp, hydecomp]
    exact hboundary p q m₁ m₂ hp hq
      (by simpa only [← hxdecomp] using hx)
      (by simpa only [← hydecomp] using hy)

/-- Form suitable for the exact kernel refinement part of v128
    Proposition prop:li-window. -/
theorem positiveWindowKernelRefines_iff_boundary
    (H : FixedFiniteMonoidHom α M) (k l : Nat) :
    PositiveWindowKernelRefines H k l ↔
      PositiveWindowBoundaryInvariant H k l := by
  constructor
  · exact positiveWindowKernel_refines_implies_boundary H k l
  · exact positiveWindowBoundary_implies_kernel_refines H k l

/-- Existing refinement monotonicity already gives the paper's RS-class
    inclusion on the nonempty-factor convention; no new learner is needed. -/
theorem fixedHSubstitutable_of_positiveWindowKernelRefines
    (H : FixedFiniteMonoidHom α M) (k l : Nat)
    (href : PositiveWindowKernelRefines H k l)
    (L : Set (Word α))
    (hsub : FixedHSubstitutable H L) :
    FixedHSubstitutable (fixedWindowMonoidHom (α := α) k l) L := by
  intro x y hx hy hxy hshared
  exact hsub hx hy (href x y hx hy hxy) hshared

/-- The corresponding original Yoshinaka (k,l)-substitutability statement. -/
theorem fixedWindowSubstitutable_of_positiveWindowKernelRefines
    (H : FixedFiniteMonoidHom α M) (k l : Nat)
    (href : PositiveWindowKernelRefines H k l)
    (L : Set (Word α))
    (hsub : FixedHSubstitutable H L) :
    FixedWindowSubstitutable k l L := by
  exact fixedWindowSubstitutable_of_fixedHSubstitutable k l L
    (fixedHSubstitutable_of_positiveWindowKernelRefines
      H k l href L hsub)

end PositiveWindowKernel

end TCS1
end LeanCfgProject
