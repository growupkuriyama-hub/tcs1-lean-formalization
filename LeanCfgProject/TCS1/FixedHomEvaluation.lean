import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v79: direct evaluation of a fixed finite-monoid typing

Section 2 represents a fixed homomorphism h : Sigma* -> M by the
multiplication table of the finite monoid together with the images of the
letters.  This file records the elementary implementation fact used by the
manuscript: h(w) is obtained by one left-to-right/right-associated scan of the
word, using exactly one monoid multiplication per letter.

The theorem is intentionally representation-level rather than a machine-code
runtime theorem.  Table lookup and one monoid multiplication are treated as
constant-cost operations because M and h are fixed over the learning class.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FixedHomEvaluation

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Precomputed image of one alphabet symbol under the fixed homomorphism. -/
def fixedHomLetterImage
    (H : FixedFiniteMonoidHom α M)
    (a : α) : M :=
  H.h [a]

/--
Direct evaluator using only the identity, the precomputed letter images, and
the monoid multiplication table.
-/
def fixedHomLetterProduct
    (H : FixedFiniteMonoidHom α M) :
    Word α → M
  | [] => 1
  | a :: w =>
      fixedHomLetterImage H a *
        fixedHomLetterProduct H w

/-- The direct finite-table evaluator computes exactly the supplied homomorphism. -/
theorem fixedHomLetterProduct_eq_h
    (H : FixedFiniteMonoidHom α M)
    (w : Word α) :
    fixedHomLetterProduct H w = H.h w := by
  induction w with
  | nil =>
      simp [fixedHomLetterProduct, H.map_nil]
  | cons a w ih =>
      simp only [fixedHomLetterProduct, fixedHomLetterImage]
      rw [ih]
      rw [show a :: w = [a] ++ w by rfl, H.map_append]

/-- Number of monoid multiplications performed by the direct evaluator. -/
def fixedHomMultiplicationCount :
    Word α → Nat
  | [] => 0
  | _ :: w => fixedHomMultiplicationCount w + 1

/-- Exactly one multiplication is performed for every input symbol. -/
@[simp] theorem fixedHomMultiplicationCount_eq_length
    (w : Word α) :
    fixedHomMultiplicationCount w = w.length := by
  induction w with
  | nil =>
      rfl
  | cons a w ih =>
      simp [fixedHomMultiplicationCount, ih]

/--
Paper-facing certificate for the Section 2 statement that a fixed h can be
evaluated in linear scan length once the finite multiplication table and
letter images are fixed.
-/
theorem fixedHom_linear_scan_certificate
    (H : FixedFiniteMonoidHom α M)
    (w : Word α) :
    fixedHomLetterProduct H w = H.h w
      ∧
    fixedHomMultiplicationCount w = w.length := by
  exact
    ⟨fixedHomLetterProduct_eq_h H w,
      fixedHomMultiplicationCount_eq_length w⟩

end FixedHomEvaluation

end TCS1
end LeanCfgProject
