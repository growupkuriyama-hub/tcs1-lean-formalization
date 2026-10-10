import LeanCfgProject.TCS1.FixedHTypeFiberRestriction

/-!
# TCS #1 v128: finite-information closure (intersection and filters)

Formalizes Proposition 3.3(i) and its regular-filtering consequence (ii)
at the language-theoretic substitutability level. The CFL closure step in
(ii) is the classical intersection-with-regular-language theorem, which is
not re-proved here. The erasing inverse-homomorphism clause (iii) remains open.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section ProductTyping

variable {α : Type u}
variable {M : Type v} {N : Type w}
variable [Monoid M] [Fintype M] [Monoid N] [Fintype N]

/-- Product of two finite-monoid typings, retaining both observations. -/
def productTyping
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N) :
    FixedFiniteMonoidHom α (M × N) where
  h x := (H.h x, G.h x)
  map_nil := by simp [H.map_nil, G.map_nil]
  map_append := by
    intro x y
    simp only [H.map_append, G.map_append]
    rfl

/-- Prop. 3.3(i): intersection is substitutable under product typing. -/
theorem fixedHSubstitutable_inter_product
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    {L J : Set (Word α)}
    (hL : FixedHSubstitutable H L)
    (hJ : FixedHSubstitutable G J) :
    FixedHSubstitutable (productTyping H G) (L ∩ J) := by
  intro x y hx hy hxy hshared
  have hxM : H.h x = H.h y := congrArg Prod.fst hxy
  have hxN : G.h x = G.h y := congrArg Prod.snd hxy
  have sharedL : HaveSharedContext L x y := by
    obtain ⟨a, b, habx, haby⟩ := hshared
    exact ⟨a, b, habx.1, haby.1⟩
  have sharedJ : HaveSharedContext J x y := by
    obtain ⟨a, b, habx, haby⟩ := hshared
    exact ⟨a, b, habx.2, haby.2⟩
  have eqL := hL hx hy hxM sharedL
  have eqJ := hJ hx hy hxN sharedJ
  apply Set.ext
  intro c
  change
    (c.1 ++ x ++ c.2 ∈ L ∩ J) ↔
    (c.1 ++ y ++ c.2 ∈ L ∩ J)
  constructor
  · intro hc
    exact ⟨(Set.ext_iff.mp eqL c).mp hc.1,
      (Set.ext_iff.mp eqJ c).mp hc.2⟩
  · intro hc
    exact ⟨(Set.ext_iff.mp eqL c).mpr hc.1,
      (Set.ext_iff.mp eqJ c).mpr hc.2⟩

/-- Prop. 3.3(ii), substitutability component of regular filtering. -/
theorem fixedHSubstitutable_regularFilter_product
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    (F : Set N)
    {L : Set (Word α)}
    (hL : FixedHSubstitutable H L) :
    FixedHSubstitutable (productTyping H G)
      (L ∩ RecognizedPreimage G F) := by
  exact fixedHSubstitutable_inter_product H G hL
    (recognizedPreimage_fixedHSubstitutable G F)

end ProductTyping

end TCS1
end LeanCfgProject
