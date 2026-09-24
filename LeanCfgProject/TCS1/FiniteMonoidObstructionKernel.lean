import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v78: finite-monoid obstruction kernel

This is the abstract obstruction used for the uncapped counter language and
for the one-bracket Dyck language in Section 9.  An infinite sequence of
nonempty factors whose pairwise distributions overlap but differ cannot be
kept apart by any fixed finite-monoid typing.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FiniteMonoidObstructionKernel

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/--
Paper-facing finite-monoid obstruction.

For an infinite Nat-indexed family of nonempty factors, if every two distinct
members have a shared context but unequal full distributions, then the target
cannot be fixed-h substitutable for any homomorphism into the finite monoid M.
-/
theorem finiteMonoid_obstruction
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (x : Nat → Word α)
    (hne : ∀ n, x n ≠ [])
    (hbad :
      ∀ {i j : Nat}, i ≠ j →
        HaveSharedContext L (x i) (x j) ∧
        Distribution L (x i) ≠ Distribution L (x j)) :
    ¬ FixedHSubstitutable H L := by
  intro hsub
  let f : Nat → M := fun n => H.h (x n)
  obtain ⟨i, j, hij, htype⟩ :=
    Finite.exists_ne_map_eq_of_infinite f
  obtain ⟨hshared, hdistNe⟩ :=
    hbad hij
  have hdist :
      Distribution L (x i) =
        Distribution L (x j) :=
    hsub (hne i) (hne j) htype hshared
  exact hdistNe hdist

/--
Uniform form: if the same bad-factor family works independently of h, then no
finite-monoid typing can make the language substitutable.
-/
theorem finiteMonoid_obstruction_uniform
    (L : Set (Word α))
    (x : Nat → Word α)
    (hne : ∀ n, x n ≠ [])
    (hbad :
      ∀ {i j : Nat}, i ≠ j →
        HaveSharedContext L (x i) (x j) ∧
        Distribution L (x i) ≠ Distribution L (x j))
    (H : FixedFiniteMonoidHom α M) :
    ¬ FixedHSubstitutable H L :=
  finiteMonoid_obstruction H L x hne hbad

end FiniteMonoidObstructionKernel

end TCS1
end LeanCfgProject
