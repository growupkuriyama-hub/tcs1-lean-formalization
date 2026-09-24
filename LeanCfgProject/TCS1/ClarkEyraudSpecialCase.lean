import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v79: Clark--Eyraud special case

The manuscript records ordinary Clark--Eyraud substitutability as a special
case of fixed-h substitutability.  This module formalizes that statement at
the generic alphabet level.

Because the Clark--Eyraud condition already equates distributions whenever
two nonempty factors share a context, the finite type equality premise is
irrelevant.  Hence a Clark--Eyraud substitutable language is fixed-h
substitutable for every fixed finite typing, and in particular for the
one-element monoid.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

/-- Generic Clark--Eyraud substitutability under the manuscript's
nonempty-factor convention. -/
def ClarkEyraudSubstitutableOn
    {α : Type u}
    (L : Set (Word α)) : Prop :=
  ∀ ⦃x y : Word α⦄,
    x ≠ [] →
    y ≠ [] →
    HaveSharedContext L x y →
    Distribution L x = Distribution L y

/-- Clark--Eyraud substitutability implies fixed-h substitutability for any h. -/
theorem fixedHSubstitutable_of_clarkEyraud
    {α : Type u}
    {M : Type v}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    {L : Set (Word α)}
    (hce : ClarkEyraudSubstitutableOn L) :
    FixedHSubstitutable H L := by
  intro x y hx hy _htype hshared
  exact hce hx hy hshared

/-- The one-element finite-monoid typing used for the paper's inclusion. -/
def trivialFiniteMonoidHom
    (α : Type u) :
    FixedFiniteMonoidHom α Unit where
  h := fun _ => ()
  map_nil := rfl
  map_append := by
    intro u v
    rfl

/--
Paper-facing Clark--Eyraud special case: every classically substitutable
language is fixed-h substitutable for the trivial finite typing.
-/
theorem clarkEyraud_special_case
    {α : Type u}
    {L : Set (Word α)}
    (hce : ClarkEyraudSubstitutableOn L) :
    FixedHSubstitutable
      (trivialFiniteMonoidHom α) L :=
  fixedHSubstitutable_of_clarkEyraud
    (trivialFiniteMonoidHom α) hce

end TCS1
end LeanCfgProject
