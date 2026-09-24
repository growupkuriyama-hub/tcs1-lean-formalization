import LeanCfgProject.TCS1.FixedWindowClassicalSubstitutability

/-!
# TCS #1 v77: exact fixed-window correspondence

The v77 manuscript states Proposition 3.3 as an exact equivalence:
for each fixed window (k,l), Yoshinaka's fixed-window substitutability is
exactly fixed-h substitutability for the concrete finite monoid homomorphism
h_{k,l}.

The forward implication was already formalized in
`FixedWindowClassicalSubstitutability`.  This file closes the converse and
packages the paper-facing iff theorem, including the (0,0) endpoint.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section FixedWindowExactEquivalence

variable {α : Type u}

/--
Converse direction of Proposition 3.3:
fixed-h substitutability for the concrete h_{k,l} implies Yoshinaka's
(k,l)-substitutability.
-/
theorem fixedWindowSubstitutable_of_fixedHSubstitutable
    [Fintype α]
    (k l : Nat)
    (L : Set (Word α))
    (hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        L) :
    FixedWindowSubstitutable k l L := by
  intro p q y₁ y₂ x₁ x₂ z₁ z₂
    hp hq hw₁ne hw₂ne hshared₁ hshared₂ hctx₁
  let w₁ : Word α := p ++ y₁ ++ q
  let w₂ : Word α := p ++ y₂ ++ q
  have hsummary :
      SameFixedWindowSummary k l w₁ w₂ := by
    by_cases hpos : 0 < k + l
    · exact
        boundary_words_sameFixedWindowSummary
          hpos p q y₁ y₂ hp hq
    · have hk : k = 0 := by omega
      have hl : l = 0 := by omega
      have hw₁ne' : w₁ ≠ [] := by
        simpa [w₁] using hw₁ne
      have hw₂ne' : w₂ ≠ [] := by
        simpa [w₂] using hw₂ne
      have hzero :
          SameFixedWindowSummary 0 0 w₁ w₂ :=
        zero_words_sameFixedWindowSummary
          (List.length_pos_of_ne_nil hw₁ne')
          (List.length_pos_of_ne_nil hw₂ne')
      simpa [hk, hl] using hzero
  have htype :
      (fixedWindowMonoidHom (α := α) k l).h w₁ =
        (fixedWindowMonoidHom (α := α) k l).h w₂ := by
    exact
      fixedWindowMonoidHom_respects
        (α := α) k l w₁ w₂ hsummary
  have hshared :
      HaveSharedContext L w₁ w₂ := by
    refine ⟨x₁, z₁, ?_, ?_⟩
    · simpa [w₁] using hshared₁
    · simpa [w₂] using hshared₂
  have hdist :
      Distribution L w₁ = Distribution L w₂ :=
    hsub hw₁ne hw₂ne htype hshared
  have hctxW₁ :
      (x₂, z₂) ∈ Distribution L w₁ := by
    simpa [Distribution, w₁] using hctx₁
  have hctxW₂ :
      (x₂, z₂) ∈ Distribution L w₂ := by
    rw [← hdist]
    exact hctxW₁
  simpa [Distribution, w₂] using hctxW₂

/--
Paper-facing exact correspondence from Proposition 3.3 of the v77 manuscript.
-/
theorem fixedWindowSubstitutable_iff_fixedHSubstitutable
    [Fintype α]
    (k l : Nat)
    (L : Set (Word α)) :
    FixedWindowSubstitutable k l L ↔
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        L := by
  constructor
  · exact
      fixedHSubstitutable_of_fixedWindowSubstitutable
        k l L
  · exact
      fixedWindowSubstitutable_of_fixedHSubstitutable
        k l L

end FixedWindowExactEquivalence

end TCS1
end LeanCfgProject
