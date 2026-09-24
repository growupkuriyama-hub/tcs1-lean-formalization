import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v79: refinement and product typings

Section 3 of the manuscript records two prose facts about the fixed typing
bias:

* a finer typing enlarges the corresponding fixed-h substitutable class; and
* two independent finite typings can be combined by their product
  homomorphism, whose kernel is the intersection of the two kernels.

The generic refinement theorem already lives in
`FixedHSubstitutability.lean`.  This module supplies the concrete product
homomorphism and packages the two class-inclusion consequences explicitly.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section FixedHTypingRefinement

variable {α : Type u}
variable {M : Type v} {N : Type w}
variable [Monoid M] [Fintype M]
variable [Monoid N] [Fintype N]

/-- Product of two fixed finite-monoid typings. -/
def productFixedFiniteMonoidHom
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N) :
    FixedFiniteMonoidHom α (M × N) where
  h word := (H.h word, G.h word)
  map_nil := by
    simp [H.map_nil, G.map_nil]
  map_append u v := by
    simp [H.map_append, G.map_append]

/--
Equality in the product typing is exactly simultaneous equality in the two
component typings.  This is the pointwise form of
ker(H × G) = ker(H) ∩ ker(G).
-/
theorem productFixedFiniteMonoidHom_eq_iff
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    (u v : Word α) :
    (productFixedFiniteMonoidHom H G).h u =
        (productFixedFiniteMonoidHom H G).h v
      ↔
    H.h u = H.h v ∧ G.h u = G.h v := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨hH, hG⟩
    exact Prod.ext hH hG

/-- The product typing refines its left component. -/
theorem productFixedFiniteMonoidHom_refines_left
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    {u v : Word α}
    (h :
      (productFixedFiniteMonoidHom H G).h u =
        (productFixedFiniteMonoidHom H G).h v) :
    H.h u = H.h v :=
  congrArg Prod.fst h

/-- The product typing refines its right component. -/
theorem productFixedFiniteMonoidHom_refines_right
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    {u v : Word α}
    (h :
      (productFixedFiniteMonoidHom H G).h u =
        (productFixedFiniteMonoidHom H G).h v) :
    G.h u = G.h v :=
  congrArg Prod.snd h

/--
Every language substitutable for the left typing remains substitutable for
the finer product typing.
-/
theorem fixedHSubstitutable_product_of_left
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    {L : Set (Word α)}
    (hsub : FixedHSubstitutable H L) :
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G) L := by
  exact
    fixedHSubstitutable_of_refinement
      H
      (productFixedFiniteMonoidHom H G)
      (fun u v huv =>
        productFixedFiniteMonoidHom_refines_left
          H G huv)
      hsub

/--
Every language substitutable for the right typing remains substitutable for
the finer product typing.
-/
theorem fixedHSubstitutable_product_of_right
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    {L : Set (Word α)}
    (hsub : FixedHSubstitutable G L) :
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G) L := by
  exact
    fixedHSubstitutable_of_refinement
      G
      (productFixedFiniteMonoidHom H G)
      (fun u v huv =>
        productFixedFiniteMonoidHom_refines_right
          H G huv)
      hsub

/--
Pointwise union form of the manuscript's class statement
RS_H ∪ RS_G ⊆ RS_{H×G}.
-/
theorem fixedHSubstitutable_product_of_either
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    {L : Set (Word α)}
    (hsub :
      FixedHSubstitutable H L ∨
        FixedHSubstitutable G L) :
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G) L := by
  rcases hsub with hH | hG
  · exact fixedHSubstitutable_product_of_left H G hH
  · exact fixedHSubstitutable_product_of_right H G hG

end FixedHTypingRefinement

end TCS1
end LeanCfgProject
