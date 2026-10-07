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


section InverseHomomorphism

universe q

variable {γ : Type q}

/-- A homomorphism between free word monoids, allowing erasing letters. -/
structure FreeWordHom (γ : Type q) (α : Type u) where
  map : Word γ → Word α
  map_nil : map [] = []
  map_append : ∀ x y : Word γ, map (x ++ y) = map x ++ map y

/-- Pull back a language along a free-word homomorphism. -/
def PullbackLanguage
    (φ : FreeWordHom γ α)
    (L : Set (Word α)) :
    Set (Word γ) :=
  {w | φ.map w ∈ L}

/-- Compose a fixed finite-monoid typing with a free-word homomorphism. -/
def composeTyping
    (H : FixedFiniteMonoidHom α M)
    (φ : FreeWordHom γ α) :
    FixedFiniteMonoidHom γ M where
  h w := H.h (φ.map w)
  map_nil := by
    rw [φ.map_nil]
    exact H.map_nil
  map_append := by
    intro x y
    rw [φ.map_append]
    exact H.map_append _ _

/-- Two-element monoid recording whether the image under φ is empty. -/
inductive EmptinessFlag where
  | empty
  | nonempty
  deriving DecidableEq, Fintype

def EmptinessFlag.mul :
    EmptinessFlag → EmptinessFlag → EmptinessFlag
  | .empty, .empty => .empty
  | _, _ => .nonempty

instance : Monoid EmptinessFlag where
  one := .empty
  mul := EmptinessFlag.mul
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl

/-- The v121 emptiness/nonemptiness flag e_φ. -/
def emptinessTyping
    (φ : FreeWordHom γ α) :
    FixedFiniteMonoidHom γ EmptinessFlag where
  h w := if φ.map w = [] then .empty else .nonempty
  map_nil := by
    rw [φ.map_nil]
    rfl
  map_append := by
    intro x y
    rw [φ.map_append]
    by_cases hx : φ.map x = [] <;>
      by_cases hy : φ.map y = [] <;>
      simp [hx, hy, EmptinessFlag.mul]

/-- The exact v121 typing (h ∘ φ) × e_φ for inverse images. -/
def inverseImageTyping
    (H : FixedFiniteMonoidHom α M)
    (φ : FreeWordHom γ α) :
    FixedFiniteMonoidHom γ (M × EmptinessFlag) :=
  productTyping (composeTyping H φ) (emptinessTyping φ)

/--
Distributional core of v121 Proposition "closure under finite information" (iii):
possibly erasing inverse homomorphisms preserve fixed-typing substitutability
after adjoining the emptiness flag.
-/
theorem fixedHSubstitutable_inverseImage
    (H : FixedFiniteMonoidHom α M)
    (φ : FreeWordHom γ α)
    {L : Set (Word α)}
    (hsub : FixedHSubstitutable H L) :
    FixedHSubstitutable
      (inverseImageTyping H φ)
      (PullbackLanguage φ L) := by
  intro x y hx hy htype hshared
  have hH :
      H.h (φ.map x) = H.h (φ.map y) := by
    exact congrArg Prod.fst htype
  have hflag :
      (emptinessTyping φ).h x =
        (emptinessTyping φ).h y := by
    exact congrArg Prod.snd htype
  by_cases hximg : φ.map x = []
  · have hyimg : φ.map y = [] := by
      by_contra hyimg
      simp [emptinessTyping, hximg, hyimg] at hflag
    apply Set.ext
    intro c
    rcases c with ⟨u, v⟩
    change
      φ.map (u ++ x ++ v) ∈ L ↔
        φ.map (u ++ y ++ v) ∈ L
    simp only [φ.map_append, List.append_assoc, hximg, hyimg,
      List.append_nil]
  · have hyimg : φ.map y ≠ [] := by
      intro hyzero
      simp [emptinessTyping, hximg, hyzero] at hflag
    rcases hshared with ⟨u, v, hxshared, hyshared⟩
    have hxL :
        φ.map u ++ φ.map x ++ φ.map v ∈ L := by
      change φ.map (u ++ x ++ v) ∈ L at hxshared
      simpa only [φ.map_append, List.append_assoc] using hxshared
    have hyL :
        φ.map u ++ φ.map y ++ φ.map v ∈ L := by
      change φ.map (u ++ y ++ v) ∈ L at hyshared
      simpa only [φ.map_append, List.append_assoc] using hyshared
    have hdist :
        Distribution L (φ.map x) =
          Distribution L (φ.map y) :=
      hsub hximg hyimg hH
        ⟨φ.map u, φ.map v, hxL, hyL⟩
    apply Set.ext
    intro c
    rcases c with ⟨p, q⟩
    change
      φ.map (p ++ x ++ q) ∈ L ↔
        φ.map (p ++ y ++ q) ∈ L
    simp only [φ.map_append, List.append_assoc]
    change
      (φ.map p, φ.map q) ∈ Distribution L (φ.map x) ↔
        (φ.map p, φ.map q) ∈ Distribution L (φ.map y)
    rw [hdist]

end InverseHomomorphism

end V121FiniteInformationClosure

end TCS1
end LeanCfgProject
