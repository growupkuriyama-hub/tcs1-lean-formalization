import LeanCfgProject.TCS1.V115PositiveImageCardinal

/-!
# TCS #1 v118: source-exact fixed-window boundary identity

The v118 manuscript replaces an external finite-semigroup citation with a
direct proof of h(p r q) = h(p q), when both boundary words have length
n = |h(Sigma+)| and the positive image is locally trivial. The exact identity
is proved here using the previously machine-checked *stronger* length-n
idempotence lemma, not by replaying v118's different prose derivation.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V118WindowSourceBridge

variable {α : Type u} {M : Type v}
variable [Fintype α] [Nonempty α] [Monoid M] [Fintype M]

/-- Middle-word erasure at positive-image cardinality, v118 Prop. 3.5. -/
theorem v118_locallyTrivial_boundary_erasure
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (p q r : Word α)
    (hp : p.length = v115PositiveImageCard H)
    (hq : q.length = v115PositiveImageCard H) :
    H.h (p ++ r ++ q) = H.h (p ++ q) := by
  have hn : 0 < v115PositiveImageCard H :=
    v115_positiveImageCard_pos H
  have hpne : p ≠ [] := by
    intro hnil
    have hzero : p.length = 0 := by simp [hnil]
    omega
  have hqne : q ≠ [] := by
    intro hnil
    have hzero : q.length = 0 := by simp [hnil]
    omega
  exact v115_locallyTrivial_boundaryErasure H hlocal p q r
    hpne hqne
    (v115_locallyTrivial_length_card_idempotent H hlocal p hp)
    (v115_locallyTrivial_length_card_idempotent H hlocal q hq)

/-- Exact forward nonempty kernel refinement, derived from boundary erasure. -/
theorem v118_locallyTrivial_window_kernel_refines
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H) :
    V115NonemptyKernelRefines
      (fixedWindowMonoidHom (α := α)
        (v115PositiveImageCard H) (v115PositiveImageCard H))
      H := by
  apply v115_windowRefinement_of_boundaryErasure
    H (v115PositiveImageCard H) (v115PositiveImageCard H)
  intro p q r hp hq
  exact v118_locallyTrivial_boundary_erasure
    H hlocal p q r hp hq

end V118WindowSourceBridge
end TCS1
end LeanCfgProject
