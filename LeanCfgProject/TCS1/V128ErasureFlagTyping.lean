import LeanCfgProject.TCS1.V128InverseImageKernel
import LeanCfgProject.TCS1.V128FiniteInformationClosure

/-!
# TCS #1 v128: finite erasure observer for Proposition 3.3(iii)

A two-element monoid distinguishes factors mapped to epsilon from
factors mapped to nonempty words. It is combined with the original
typing to show substitution closure under erasing inverse images.

This formalizes the substitutability component, not the independently
needed CFL closure under inverse homomorphisms.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

inductive ErasureFlag where
  | erased
  | present
deriving DecidableEq, Fintype

instance : Monoid ErasureFlag where
  one := .erased
  mul a b := match a, b with
    | .erased, .erased => .erased
    | _, _ => .present
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  mul_assoc a b c := by
    cases a <;> cases b <;> cases c <;> rfl

section ErasureFlagTyping

variable {α : Type u} {β : Type v} {M : Type w}
variable [Monoid M] [Fintype M]

def erasureFlagValue (φ : Word β → Word α) (x : Word β) : ErasureFlag :=
  if φ x = [] then .erased else .present

theorem erasureFlagValue_erased_iff
    (φ : Word β → Word α) (x : Word β) :
    erasureFlagValue φ x = ErasureFlag.erased ↔ φ x = [] := by
  by_cases h : φ x = []
  · simp [erasureFlagValue, h]
  · simp [erasureFlagValue, h]

theorem erasureFlagValue_append
    (φ : Word β → Word α)
    (φ_append : ∀ x y, φ (x ++ y) = φ x ++ φ y)
    (x y : Word β) :
    erasureFlagValue φ (x ++ y) =
      erasureFlagValue φ x * erasureFlagValue φ y := by
  simp only [erasureFlagValue, φ_append]
  cases hx : φ x with
  | nil =>
      cases hy : φ y with
      | nil => simp [hx, hy]
      | cons b bs => simp [hx, hy]
  | cons a as =>
      cases hy : φ y with
      | nil => simp [hx, hy]
      | cons b bs => simp [hx, hy]

/-- The erasure status is itself a fixed finite-monoid typing. -/
def erasureFlagTyping
    (φ : Word β → Word α)
    (φ_nil : φ [] = [])
    (φ_append : ∀ x y, φ (x ++ y) = φ x ++ φ y) :
    FixedFiniteMonoidHom β ErasureFlag where
  h := erasureFlagValue φ
  map_nil := by
    change erasureFlagValue φ [] = (1 : ErasureFlag)
    simp [erasureFlagValue, φ_nil]
  map_append := erasureFlagValue_append φ φ_append

/-- Precomposition of a finite typing with an arbitrary word morphism. -/
def precomposedTyping
    (H : FixedFiniteMonoidHom α M)
    (φ : Word β → Word α)
    (φ_nil : φ [] = [])
    (φ_append : ∀ x y, φ (x ++ y) = φ x ++ φ y) :
    FixedFiniteMonoidHom β M where
  h x := H.h (φ x)
  map_nil := by
    change H.h (φ []) = 1
    rw [φ_nil]
    exact H.map_nil
  map_append := by
    intro x y
    change H.h (φ (x ++ y)) = H.h (φ x) * H.h (φ y)
    rw [φ_append]
    exact H.map_append (φ x) (φ y)

/-- Manuscript observer: (h composed with phi) times the erasure flag. -/
def erasingInverseTyping
    (H : FixedFiniteMonoidHom α M)
    (φ : Word β → Word α)
    (φ_nil : φ [] = [])
    (φ_append : ∀ x y, φ (x ++ y) = φ x ++ φ y) :
    FixedFiniteMonoidHom β (M × ErasureFlag) :=
  productTyping (precomposedTyping H φ φ_nil φ_append)
    (erasureFlagTyping φ φ_nil φ_append)

/-- Proposition 3.3(iii): substitutability under erasing inverse images. -/
theorem inverseImage_fixedHSubstitutable_with_erasureFlag
    (H : FixedFiniteMonoidHom α M)
    (φ : Word β → Word α)
    (φ_nil : φ [] = [])
    (φ_append : ∀ x y, φ (x ++ y) = φ x ++ φ y)
    (L : Set (Word α))
    (hsub : FixedHSubstitutable H L) :
    FixedHSubstitutable
      (erasingInverseTyping H φ φ_nil φ_append)
      (wordInverseImage φ L) := by
  apply inverseImage_fixedHSubstitutable_of_observer
    H (erasingInverseTyping H φ φ_nil φ_append)
      φ φ_append L hsub
  · intro x y hxy
    exact congrArg Prod.fst hxy
  · intro x y hxy
    have hbit : erasureFlagValue φ x = erasureFlagValue φ y :=
      congrArg Prod.snd hxy
    calc
      (φ x = []) ↔ erasureFlagValue φ x = ErasureFlag.erased :=
        (erasureFlagValue_erased_iff φ x).symm
      _ ↔ erasureFlagValue φ y = ErasureFlag.erased := by rw [hbit]
      _ ↔ (φ y = []) := erasureFlagValue_erased_iff φ y

end ErasureFlagTyping

end TCS1
end LeanCfgProject
