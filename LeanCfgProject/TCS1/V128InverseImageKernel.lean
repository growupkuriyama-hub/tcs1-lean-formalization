import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v128: erasing inverse-image distribution kernel

Proposition 3.3(iii), semantic heart of the proof. A future finite-monoid
observer module must construct the product (h ∘ phi, e_phi) and show equal
product values imply the two comparison hypotheses below. CFL closure under
inverse homomorphism is independent of this lemma.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section InverseImageKernel

variable {α : Type u} {β : Type v} {M : Type w}
variable [Monoid M] [Fintype M]

/-- Language inverse image for an arbitrary word map. -/
def wordInverseImage (φ : Word β → Word α)
    (L : Set (Word α)) : Set (Word β) :=
  {x | φ x ∈ L}

/-- Inverse-image substitutability, provided the typing can detect erasure. -/
theorem inverseImage_fixedHSubstitutable_kernel
    (H : FixedFiniteMonoidHom α M)
    (φ : Word β → Word α)
    (φ_append : ∀ x y, φ (x ++ y) = φ x ++ φ y)
    (L : Set (Word α))
    (hsub : FixedHSubstitutable H L)
    {x y : Word β}
    (himageType : H.h (φ x) = H.h (φ y))
    (herase : (φ x = []) ↔ (φ y = []))
    (hshared : HaveSharedContext (wordInverseImage φ L) x y) :
    Distribution (wordInverseImage φ L) x =
      Distribution (wordInverseImage φ L) y := by
  by_cases hxempty : φ x = []
  · have hyempty : φ y = [] := herase.mp hxempty
    apply Set.ext
    intro c
    change
      (φ (c.1 ++ x ++ c.2) ∈ L) ↔
      (φ (c.1 ++ y ++ c.2) ∈ L)
    simp only [φ_append, hxempty, hyempty, List.nil_append]
  · have hyempty : φ y ≠ [] := by
      intro hy
      exact hxempty (herase.mpr hy)
    obtain ⟨a, b, ha, hb⟩ := hshared
    have hsharedImage : HaveSharedContext L (φ x) (φ y) := by
      refine ⟨φ a, φ b, ?_, ?_⟩
      · simpa only [wordInverseImage, Set.mem_setOf_eq,
          φ_append] using ha
      · simpa only [wordInverseImage, Set.mem_setOf_eq,
          φ_append] using hb
    have hdist := hsub hxempty hyempty himageType hsharedImage
    apply Set.ext
    intro c
    have hc := Set.ext_iff.mp hdist (φ c.1, φ c.2)
    change
      (φ (c.1 ++ x ++ c.2) ∈ L) ↔
      (φ (c.1 ++ y ++ c.2) ∈ L)
    simpa only [Distribution, Set.mem_setOf_eq,
      φ_append] using hc

end InverseImageKernel

end TCS1
end LeanCfgProject
