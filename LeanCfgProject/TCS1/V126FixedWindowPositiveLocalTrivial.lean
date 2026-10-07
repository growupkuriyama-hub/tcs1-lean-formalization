import LeanCfgProject.TCS1.FixedWindowConcreteMonoid
import Mathlib.Tactic

/-!
# TCS #1 v126: local triviality of the positive fixed-window image

The manuscript's Proposition on locally trivial typings uses that the positive
image of every concrete fixed-window typing h_{k,l} is locally trivial.

Because the monoid carrier also contains the empty-word summary, the correct
statement is deliberately about the **positive image**.  We formalize it as a
predicate on elements of the concrete image monoid and prove directly that

  e * t * e = e

whenever e and t have nonempty word representatives and e is idempotent.

This closes the fixed-window -> locally-trivial direction without importing a
separate semigroup theorem.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section V126FixedWindowPositiveLocalTrivial

variable {α : Type u} [Fintype α]

/-- Membership in the positive image h_{k,l}(Sigma+), represented inside the
full image monoid h_{k,l}(Sigma*). -/
def FixedWindowPositiveImage
    (k l : Nat)
    (s : FixedWindowMonoid α k l) : Prop :=
  ∃ w : Word α,
    w ≠ [] ∧
    (fixedWindowMonoidHom (α := α) k l).h w = s

/-- A nonempty representative of an idempotent positive-image element must be
in the long-word part of the tagged fixed-window summary. -/
theorem fixedWindow_positive_idempotent_long
    (k l : Nat)
    {e : FixedWindowMonoid α k l}
    {x : Word α}
    (hxne : x ≠ [])
    (hx : (fixedWindowMonoidHom (α := α) k l).h x = e)
    (he : e * e = e) :
    fixedWindowThreshold k l ≤ x.length := by
  let H := fixedWindowMonoidHom (α := α) k l
  have hxx : H.h (x ++ x) = H.h x := by
    calc
      H.h (x ++ x) = H.h x * H.h x := H.map_append x x
      _ = e * e := by rw [hx]
      _ = e := he
      _ = H.h x := hx.symm
  have hsame :
      SameFixedWindowSummary k l (x ++ x) x :=
    fixedWindowMonoidHom_reflects
      (α := α) k l (x ++ x) x hxx
  rcases hsame with hshort | hlong
  · rcases hshort with ⟨_, heq⟩
    have hlen := congrArg List.length heq
    have hxpos : 0 < x.length := List.length_pos.mpr hxne
    simp only [List.length_append] at hlen
    omega
  · exact hlong.2.1

/-- A long word has the same fixed-window summary as itself with an arbitrary
middle word inserted between two copies: x y x and x have the same boundary
windows. -/
theorem fixedWindow_long_sandwich_same
    (k l : Nat)
    {x y : Word α}
    (hxlong : fixedWindowThreshold k l ≤ x.length) :
    SameFixedWindowSummary k l (x ++ y ++ x) x := by
  have hfit : k + l ≤ x.length :=
    fixedWindow_sum_le_of_cut (α := α) hxlong
  obtain ⟨m, hxm⟩ :=
    exists_fixedWindow_middle x k l hfit
  let p : Word α := x.take k
  let q : Word α := x.drop (x.length - l)
  have hp : p.length = k := by
    dsimp [p]
    exact fixedWindow_prefix_length x k l hfit
  have hq : q.length = l := by
    dsimp [q]
    exact fixedWindow_suffix_length x k l hfit
  let m₂ : Word α :=
    m ++ q ++ y ++ p ++ m
  have hxshape : x = p ++ m ++ q := by
    simpa [p, q] using hxm
  have hsandshape :
      x ++ y ++ x = p ++ m₂ ++ q := by
    rw [hxshape]
    simp only [m₂, List.append_assoc]
  have hsandlong :
      fixedWindowThreshold k l ≤ (x ++ y ++ x).length := by
    simp only [List.length_append]
    omega
  exact
    Or.inr
      ⟨hsandlong, hxlong,
        p, q, m₂, m,
        hp, hq,
        hsandshape, hxshape⟩

/-- The positive image semigroup of h_{k,l} is locally trivial in exactly the
manuscript's ete=e sense. -/
theorem fixedWindow_positive_image_locally_trivial
    (k l : Nat) :
    ∀ e : FixedWindowMonoid α k l,
      FixedWindowPositiveImage k l e →
      e * e = e →
      ∀ t : FixedWindowMonoid α k l,
        FixedWindowPositiveImage k l t →
        e * t * e = e := by
  intro e hepos heidem t htpos
  rcases hepos with ⟨x, hxne, hx⟩
  rcases htpos with ⟨y, hyne, hy⟩
  let H := fixedWindowMonoidHom (α := α) k l
  have hxlong :
      fixedWindowThreshold k l ≤ x.length :=
    fixedWindow_positive_idempotent_long
      (α := α) k l hxne hx heidem
  have hsame :
      SameFixedWindowSummary k l (x ++ y ++ x) x :=
    fixedWindow_long_sandwich_same
      (α := α) k l hxlong
  have htypes :
      H.h (x ++ y ++ x) = H.h x :=
    fixedWindowMonoidHom_respects
      (α := α) k l (x ++ y ++ x) x hsame
  calc
    e * t * e
        = H.h x * H.h y * H.h x := by
            rw [hx, hy]
    _ = H.h (x ++ y ++ x) := by
          rw [H.map_append, H.map_append]
    _ = H.h x := htypes
    _ = e := hx

end V126FixedWindowPositiveLocalTrivial

end TCS1
end LeanCfgProject
