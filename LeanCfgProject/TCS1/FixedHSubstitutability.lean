import Mathlib

/-!
# TCS #1 v63: fixed-h substitutability kernel

This module restarts the Lean verification of the current TCS #1 revision
"Distributional Learning of Context-Free Languages under Fixed Finite-Monoid
Typing" from the v63 manuscript baseline.

The first layer formalizes the language-theoretic core used in Section 3:

* two-sided distributions;
* fixed-h substitutability on nonempty internal factors;
* monotonicity under refinement of the fixed typing;
* the sufficient syntactic-refinement criterion; and
* the fact that a language recognized directly by the fixed finite monoid is
  fixed-h substitutable.

This file is intentionally independent of the older two-sided descriptor /
residual-concept development and of the MCFG formalization.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

/-- Words are finite lists. -/
abbrev Word (α : Type u) := List α

/--
An explicit homomorphism from the free word monoid into a fixed finite monoid.
The paper represents such a homomorphism by the multiplication table and the
letter images; for the proofs below, only preservation of the empty word and
concatenation is needed.
-/
structure FixedFiniteMonoidHom
    (α : Type u) (M : Type v) [Monoid M] [Fintype M] where
  h : Word α → M
  map_nil : h [] = 1
  map_append : ∀ u v : Word α, h (u ++ v) = h u * h v

/-- The two-sided distribution of an internal factor in a language. -/
def Distribution
    {α : Type u}
    (L : Set (Word α))
    (x : Word α) :
    Set (Word α × Word α) :=
  { c | c.1 ++ x ++ c.2 ∈ L }

/-- A concrete formulation of nonempty intersection of two distributions. -/
def HaveSharedContext
    {α : Type u}
    (L : Set (Word α))
    (x y : Word α) : Prop :=
  ∃ u v : Word α,
    u ++ x ++ v ∈ L ∧
    u ++ y ++ v ∈ L

theorem sharedContext_iff_distribution_inter_nonempty
    {α : Type u}
    {L : Set (Word α)}
    {x y : Word α} :
    HaveSharedContext L x y ↔
      (Distribution L x ∩ Distribution L y).Nonempty := by
  constructor
  · rintro ⟨u, v, hx, hy⟩
    refine ⟨(u, v), ?_, ?_⟩
    · simpa [Distribution] using hx
    · simpa [Distribution] using hy
  · rintro ⟨c, hx, hy⟩
    refine ⟨c.1, c.2, ?_, ?_⟩
    · simpa [Distribution] using hx
    · simpa [Distribution] using hy

/--
Definition 2.2 / Section 3 of the v63 manuscript:
only nonempty internal factors are compared.
-/
def FixedHSubstitutable
    {α : Type u}
    {M : Type v} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α)) : Prop :=
  ∀ ⦃x y : Word α⦄,
    x ≠ [] →
    y ≠ [] →
    H.h x = H.h y →
    HaveSharedContext L x y →
    Distribution L x = Distribution L y

/--
Equality of fixed-h types is preserved when the same left and right context
is attached.  This is the algebraic step used repeatedly in the paper.
-/
theorem context_image_eq
    {α : Type u}
    {M : Type v} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    {x y : Word α}
    (hxy : H.h x = H.h y)
    (u v : Word α) :
    H.h (u ++ x ++ v) = H.h (u ++ y ++ v) := by
  rw [H.map_append (u ++ x) v, H.map_append (u ++ y) v]
  rw [H.map_append u x, H.map_append u y, hxy]

/--
Monotonicity under refinement of the typing bias:
if equality under Hfine implies equality under Hcoarse, then every
Hcoarse-substitutable language is Hfine-substitutable.
-/
theorem fixedHSubstitutable_of_refinement
    {α : Type u}
    {M : Type v} {N : Type w}
    [Monoid M] [Fintype M]
    [Monoid N] [Fintype N]
    (Hcoarse : FixedFiniteMonoidHom α M)
    (Hfine : FixedFiniteMonoidHom α N)
    {L : Set (Word α)}
    (hrefines :
      ∀ u v : Word α,
        Hfine.h u = Hfine.h v →
        Hcoarse.h u = Hcoarse.h v)
    (hsub : FixedHSubstitutable Hcoarse L) :
    FixedHSubstitutable Hfine L := by
  intro x y hx hy hxy hshared
  exact hsub hx hy (hrefines x y hxy) hshared

/--
A sufficient criterion used in Section 3:
if equal h-types already imply equality of full distributions, then the
language is fixed-h substitutable.
-/
theorem fixedHSubstitutable_of_type_implies_distribution_eq
    {α : Type u}
    {M : Type v} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    {L : Set (Word α)}
    (hrefines :
      ∀ x y : Word α,
        x ≠ [] →
        y ≠ [] →
        H.h x = H.h y →
        Distribution L x = Distribution L y) :
    FixedHSubstitutable H L := by
  intro x y hx hy hxy _hshared
  exact hrefines x y hx hy hxy

/-- The language recognized directly by H with accepting set Acc. -/
def RecognizedPreimage
    {α : Type u}
    {M : Type v} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    (Acc : Set M) :
    Set (Word α) :=
  { w | H.h w ∈ Acc }

/--
The second statement of Proposition 3.1 in the v63 manuscript:
for every accepting subset of the fixed finite monoid, its inverse image is
fixed-h substitutable.
-/
theorem recognizedPreimage_fixedHSubstitutable
    {α : Type u}
    {M : Type v} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    (Acc : Set M) :
    FixedHSubstitutable H (RecognizedPreimage H Acc) := by
  intro x y _hx _hy hxy _hshared
  apply Set.ext
  intro c
  change
    (H.h (c.1 ++ x ++ c.2) ∈ Acc) ↔
      (H.h (c.1 ++ y ++ c.2) ∈ Acc)
  rw [context_image_eq H hxy c.1 c.2]

end TCS1
end LeanCfgProject
