import LeanCfgProject.TCS1.FiniteMonoidObstructionKernel

/-!
# TCS #1 v158: `lem:finite-monoid-obstruction` with an infinite set `Ξ`

The manuscript states the obstruction for an infinite set `Ξ ⊆ Σ⁺` whose
distinct elements pairwise share a context but have different distributions.
`finiteMonoid_obstruction` is stated for a sequence; this file derives the set
form through an injective enumeration of `Ξ`.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

theorem finiteMonoid_obstruction_set {α : Type u} {M : Type v} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M) (L : Set (Word α)) (Ξ : Set (Word α))
    (hinf : Ξ.Infinite) (hne : ∀ x, x ∈ Ξ → x ≠ [])
    (hbad : ∀ x, x ∈ Ξ → ∀ y, y ∈ Ξ → x ≠ y →
      HaveSharedContext L x y ∧ Distribution L x ≠ Distribution L y) :
    ¬ FixedHSubstitutable H L := by
  let e := hinf.natEmbedding
  exact finiteMonoid_obstruction H L (fun n => (e n).1) (fun n => hne _ (e n).2)
    (fun {i j} hij => hbad _ (e i).2 _ (e j).2
      (fun h => hij (e.injective (Subtype.ext h))))

/--
info: 'LeanCfgProject.TCS1.finiteMonoid_obstruction_set' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms finiteMonoid_obstruction_set

end TCS1
end LeanCfgProject
