import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v121: finite-information closure, Lean core

This file formalizes the new fixed-typing part of Proposition
"closure under finite information" in the v121 manuscript.

The context-free closure facts used by the paper (CFL closure under
intersection with a regular language and under inverse homomorphism) remain
classical external background.  The genuinely fixed-h distributional step is
proved here without axioms.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V121FiniteInformationClosure

variable {α : Type u}
variable {M : Type v} {N : Type w}
variable [Monoid M] [Fintype M]
variable [Monoid N] [Fintype N]

/-- Product of two fixed finite-monoid typings. -/
def productTyping
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N) :
    FixedFiniteMonoidHom α (M × N) where
  h x := (H.h x, G.h x)
  map_nil := by
    simp [H.map_nil, G.map_nil]
  map_append := by
    intro x y
    simp [H.map_append, G.map_append]

@[simp] theorem productTyping_fst
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    (x : Word α) :
    (productTyping H G).h x |>.1 = H.h x :=
  rfl

@[simp] theorem productTyping_snd
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    (x : Word α) :
    (productTyping H G).h x |>.2 = G.h x :=
  rfl

/-- Distributional part of v121 Proposition "closure under finite information" (i). -/
theorem fixedHSubstitutable_inter_product
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    {L J : Set (Word α)}
    (hL : FixedHSubstitutable H L)
    (hJ : FixedHSubstitutable G J) :
    FixedHSubstitutable
      (productTyping H G)
      (L ∩ J) := by
  intro x y hx hy htype hshared
  have hH : H.h x = H.h y :=
    congrArg Prod.fst htype
  have hG : G.h x = G.h y :=
    congrArg Prod.snd htype
  rcases hshared with ⟨u, v, hxIJ, hyIJ⟩
  have hdistL : Distribution L x = Distribution L y :=
    hL hx hy hH ⟨u, v, hxIJ.1, hyIJ.1⟩
  have hdistJ : Distribution J x = Distribution J y :=
    hJ hx hy hG ⟨u, v, hxIJ.2, hyIJ.2⟩
  apply Set.ext
  intro c
  constructor
  · intro hc
    have hcL : c ∈ Distribution L x := by
      exact hc.1
    have hcJ : c ∈ Distribution J x := by
      exact hc.2
    rw [hdistL] at hcL
    rw [hdistJ] at hcJ
    exact ⟨hcL, hcJ⟩
  · intro hc
    have hcL : c ∈ Distribution L y := by
      exact hc.1
    have hcJ : c ∈ Distribution J y := by
      exact hc.2
    rw [← hdistL] at hcL
    rw [← hdistJ] at hcJ
    exact ⟨hcL, hcJ⟩

/--
Distributional part of v121 Proposition "closure under finite information" (ii):
intersecting an H-substitutable language with a language recognized by G is
substitutable for the product typing.
-/
theorem fixedHSubstitutable_inter_recognized_product
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    (Acc : Set N)
    {L : Set (Word α)}
    (hL : FixedHSubstitutable H L) :
    FixedHSubstitutable
      (productTyping H G)
      (L ∩ RecognizedPreimage G Acc) := by
  exact
    fixedHSubstitutable_inter_product
      H G hL
      (recognizedPreimage_fixedHSubstitutable G Acc)

end V121FiniteInformationClosure

end TCS1
end LeanCfgProject
