import LeanCfgProject.TCS1.V126ExactSourceAudit
import LeanCfgProject.TCS1.FixedWindowConcreteMonoid
import LeanCfgProject.TCS1.ReconstructionSoundness

/-!
# TCS #1 v128: exact audit of final precision edits

The v128 manuscript does not introduce a stronger mathematical theorem than
the already checked v126 line.  It makes two previously implicit scope points
explicit in the English source:

1. for distinct observed nonempty factors, equality of h_{k,l}-type is the
   long-word case, i.e. both factors have length at least
   max{1,k+l} and share the length-k prefix and length-l suffix;
2. the empty target is handled separately by the empty sample.

This file proves those two source-facing claims directly.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section V128SourcePrecisionAudit

variable {α : Type u}

/-- The manuscript cutoff is literally max{1,k+l}. -/
theorem v128_fixedWindowThreshold_exact
    (k l : Nat) :
    fixedWindowThreshold k l = max 1 (k + l) := by
  rfl

/--
For two distinct words, equality of the concrete fixed-window type is
equivalent to the long-word branch of the tagged summary.

This is the exact algebraic content of the v128 clarification of the
nontrivial unary-rule comparison with Yoshinaka's constructor.
-/
theorem v128_fixedWindow_type_eq_iff_long_of_ne
    [Fintype α]
    (k l : Nat)
    {x y : Word α}
    (hxy : x ≠ y) :
    (fixedWindowMonoidHom (α := α) k l).h x =
        (fixedWindowMonoidHom (α := α) k l).h y
      ↔
    fixedWindowThreshold k l ≤ x.length ∧
      fixedWindowThreshold k l ≤ y.length ∧
      ∃ p q m₁ m₂ : Word α,
        p.length = k ∧
        q.length = l ∧
        x = p ++ m₁ ++ q ∧
        y = p ++ m₂ ++ q := by
  constructor
  · intro htype
    have hsame :
        SameFixedWindowSummary k l x y :=
      fixedWindowMonoidHom_reflects
        (α := α) k l x y htype
    rcases hsame with hshort | hlong
    · rcases hshort with ⟨_hxshort, hyx⟩
      exact False.elim (hxy hyx.symm)
    · exact hlong
  · intro hlong
    exact
      fixedWindowMonoidHom_respects
        (α := α) k l x y (Or.inr hlong)

/-- Empty positive sample reconstructs exactly the empty language. -/
theorem v128_batchLanguage_empty_sample
    {M : Type} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M) :
    BatchLanguage H (∅ : Finset (Word α)) =
      (∅ : Set (Word α)) := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    cases hw with
    | nonempty hs hs_ne d =>
        simp at hs
    | epsilon heps =>
        simp at heps
  · intro hw
    simp at hw

/-- Paper-facing formulation: the empty target has the empty sample as exact
characteristic data for the batch reconstruction operator. -/
theorem v128_empty_target_handled_by_empty_sample
    {M : Type} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M) :
    ∃ C : Finset (Word α),
      (↑C : Set (Word α)) ⊆ (∅ : Set (Word α)) ∧
      BatchLanguage H C = (∅ : Set (Word α)) := by
  refine ⟨∅, ?_, v128_batchLanguage_empty_sample H⟩
  simp

end V128SourcePrecisionAudit

end TCS1
end LeanCfgProject
