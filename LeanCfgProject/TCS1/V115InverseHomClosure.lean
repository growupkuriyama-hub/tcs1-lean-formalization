import LeanCfgProject.TCS1.V115FiniteInformationClosure

/-!
# TCS #1 v115: inverse-homomorphism closure, substitutability core

This module formalizes the language-theoretic part of Proposition 3.2(iii)
from the v115 manuscript.

A free-monoid homomorphism Gamma* -> Sigma* is represented by its letter
images and extended by List.flatMap.  To handle erasing homomorphisms exactly
as in the paper, the pullback typing is augmented by a two-element emptiness
monoid.  Equality of the augmented types therefore distinguishes the case
where both internal-factor images are empty from the case where both are
nonempty.

The context-free closure of CFL under inverse homomorphism is not claimed here;
this file proves the fixed-h substitutability component that is specific to the
paper.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V115InverseHomClosure

variable {α : Type u}
variable {β : Type v}
variable {M : Type w} [Monoid M] [Fintype M]

/-- Extension of a letter-to-word map to the induced free-monoid homomorphism. -/
def v115WordSubstitution
    (φ : β → Word α) (w : Word β) : Word α :=
  w.flatMap φ

@[simp] theorem v115WordSubstitution_nil
    (φ : β → Word α) :
    v115WordSubstitution φ [] = [] := by
  rfl

@[simp] theorem v115WordSubstitution_append
    (φ : β → Word α)
    (u v : Word β) :
    v115WordSubstitution φ (u ++ v) =
      v115WordSubstitution φ u ++
        v115WordSubstitution φ v := by
  simp [v115WordSubstitution]

/-- Two-element monoid recording whether a word is empty. -/
inductive V115EmptinessFlag
  | empty
  | nonempty
  deriving DecidableEq, Fintype

namespace V115EmptinessFlag

def mul : V115EmptinessFlag → V115EmptinessFlag → V115EmptinessFlag
  | empty, empty => empty
  | _, _ => nonempty

instance : One V115EmptinessFlag :=
  ⟨empty⟩

instance : Mul V115EmptinessFlag :=
  ⟨mul⟩

instance : Monoid V115EmptinessFlag where
  one := empty
  mul := mul
  one_mul a := by
    cases a <;> rfl
  mul_one a := by
    cases a <;> rfl
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;> rfl

end V115EmptinessFlag

/-- Empty words map to the identity; every nonempty word maps to the zero-like state. -/
def v115WordEmptiness :
    Word α → V115EmptinessFlag
  | [] => .empty
  | _ :: _ => .nonempty

@[simp] theorem v115WordEmptiness_eq_empty_iff
    (w : Word α) :
    v115WordEmptiness w = .empty ↔ w = [] := by
  cases w <;> simp [v115WordEmptiness]

@[simp] theorem v115WordEmptiness_append
    (u v : Word α) :
    v115WordEmptiness (u ++ v) =
      v115WordEmptiness u * v115WordEmptiness v := by
  cases u <;> cases v <;> rfl

/-- The two-element finite-monoid homomorphism detecting emptiness. -/
def v115WordEmptinessHom :
    FixedFiniteMonoidHom α V115EmptinessFlag where
  h := v115WordEmptiness
  map_nil := rfl
  map_append := v115WordEmptiness_append

/-- Pull a fixed typing back along the free-monoid homomorphism induced by φ. -/
def v115PullbackTyping
    (H : FixedFiniteMonoidHom α M)
    (φ : β → Word α) :
    FixedFiniteMonoidHom β M where
  h w := H.h (v115WordSubstitution φ w)
  map_nil := by
    simp [H.map_nil]
  map_append u v := by
    rw [v115WordSubstitution_append, H.map_append]

/--
The paper's augmented inverse-image typing:
(h ∘ φ) together with the bit recording whether φ(w) is empty.
-/
def v115InverseImageTyping
    (H : FixedFiniteMonoidHom α M)
    (φ : β → Word α) :
    FixedFiniteMonoidHom β (M × V115EmptinessFlag) :=
  productFixedFiniteMonoidHom
    (v115PullbackTyping H φ)
    (v115PullbackTyping
      (v115WordEmptinessHom (α := α)) φ)

/-- Inverse image of a language under the induced free-monoid homomorphism. -/
def v115SubstitutionPreimage
    (φ : β → Word α)
    (L : Set (Word α)) :
    Set (Word β) :=
  { w | v115WordSubstitution φ w ∈ L }

/--
Substitutability core of manuscript Proposition 3.2(iii).

The emptiness component is essential when φ erases letters: if the two factor
images are empty, their source-side distributions agree directly; otherwise
both images are nonempty and fixed-h substitutability of L applies.
-/
theorem fixedHSubstitutable_substitutionPreimage
    (H : FixedFiniteMonoidHom α M)
    (φ : β → Word α)
    {L : Set (Word α)}
    (hsub : FixedHSubstitutable H L) :
    FixedHSubstitutable
      (v115InverseImageTyping H φ)
      (v115SubstitutionPreimage φ L) := by
  intro x y _hx _hy hxy hshared
  have hHxy :
      (v115PullbackTyping H φ).h x =
        (v115PullbackTyping H φ).h y :=
    productFixedFiniteMonoidHom_refines_left
      (v115PullbackTyping H φ)
      (v115PullbackTyping
        (v115WordEmptinessHom (α := α)) φ)
      hxy
  have hExy :
      (v115PullbackTyping
          (v115WordEmptinessHom (α := α)) φ).h x =
        (v115PullbackTyping
          (v115WordEmptinessHom (α := α)) φ).h y :=
    productFixedFiniteMonoidHom_refines_right
      (v115PullbackTyping H φ)
      (v115PullbackTyping
        (v115WordEmptinessHom (α := α)) φ)
      hxy
  change
    H.h (v115WordSubstitution φ x) =
      H.h (v115WordSubstitution φ y)
    at hHxy
  change
    v115WordEmptiness (v115WordSubstitution φ x) =
      v115WordEmptiness (v115WordSubstitution φ y)
    at hExy
  by_cases hx0 : v115WordSubstitution φ x = []
  · have hy0 : v115WordSubstitution φ y = [] := by
      apply
        (v115WordEmptiness_eq_empty_iff
          (v115WordSubstitution φ y)).mp
      rw [← hExy]
      exact
        (v115WordEmptiness_eq_empty_iff
          (v115WordSubstitution φ x)).2 hx0
    apply Set.ext
    intro c
    change
      v115WordSubstitution φ (c.1 ++ x ++ c.2) ∈ L ↔
        v115WordSubstitution φ (c.1 ++ y ++ c.2) ∈ L
    simp [hx0, hy0, List.append_assoc]
  · have hy0 : v115WordSubstitution φ y ≠ [] := by
      intro hy
      apply hx0
      apply
        (v115WordEmptiness_eq_empty_iff
          (v115WordSubstitution φ x)).mp
      rw [hExy]
      exact
        (v115WordEmptiness_eq_empty_iff
          (v115WordSubstitution φ y)).2 hy
    rcases hshared with ⟨u, v, hux, huy⟩
    have hsharedImage :
        HaveSharedContext L
          (v115WordSubstitution φ x)
          (v115WordSubstitution φ y) := by
      refine
        ⟨v115WordSubstitution φ u,
         v115WordSubstitution φ v, ?_, ?_⟩
      · change v115WordSubstitution φ (u ++ x ++ v) ∈ L at hux
        simpa [List.append_assoc] using hux
      · change v115WordSubstitution φ (u ++ y ++ v) ∈ L at huy
        simpa [List.append_assoc] using huy
    have hdist :
        Distribution L (v115WordSubstitution φ x) =
          Distribution L (v115WordSubstitution φ y) :=
      hsub hx0 hy0 hHxy hsharedImage
    apply Set.ext
    intro c
    have hc :=
      Set.ext_iff.mp hdist
        (v115WordSubstitution φ c.1,
         v115WordSubstitution φ c.2)
    change
      v115WordSubstitution φ (c.1 ++ x ++ c.2) ∈ L ↔
        v115WordSubstitution φ (c.1 ++ y ++ c.2) ∈ L
    simpa [Distribution, List.append_assoc] using hc

end V115InverseHomClosure

end TCS1
end LeanCfgProject
