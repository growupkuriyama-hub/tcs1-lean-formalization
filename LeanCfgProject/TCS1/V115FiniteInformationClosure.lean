import LeanCfgProject.TCS1.FixedHTypingRefinement

/-!
# TCS #1 v115: finite-information closure, language-theoretic core

The v115 manuscript adds Proposition 3.2 ("closure under finite information").
This module starts the v115 re-verification with the part that is internal to
the fixed-h substitutability formalism.

For two fixed finite-monoid typings H and G, intersection of an
H-substitutable language with a G-substitutable language is substitutable for
the product typing H × G.  As an immediate specialization, intersecting an
H-substitutable language with a language recognized directly by G is
substitutable for H × G.

The context-free-language closure statements in manuscript Proposition 3.2(ii)
are representation-level consequences and are deliberately not claimed by
this file.  They will be attached to the v115 audit only after the corresponding
CFG/regular-intersection bridge is machine-checked.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V115FiniteInformationClosure

variable {α : Type u}
variable {M : Type v} {N : Type w}
variable [Monoid M] [Fintype M]
variable [Monoid N] [Fintype N]

/--
Language-theoretic core of Proposition 3.2(i).

If L is substitutable for H and K is substitutable for G, then L ∩ K is
substitutable for the product typing H × G.
-/
theorem fixedHSubstitutable_inter_product
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    {L K : Set (Word α)}
    (hL : FixedHSubstitutable H L)
    (hK : FixedHSubstitutable G K) :
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G)
      (L ∩ K) := by
  intro x y hx hy hxy hshared
  have hHxy : H.h x = H.h y :=
    productFixedFiniteMonoidHom_refines_left H G hxy
  have hGxy : G.h x = G.h y :=
    productFixedFiniteMonoidHom_refines_right H G hxy
  rcases hshared with ⟨u, v, hxBoth, hyBoth⟩
  have hsharedL : HaveSharedContext L x y :=
    ⟨u, v, hxBoth.1, hyBoth.1⟩
  have hsharedK : HaveSharedContext K x y :=
    ⟨u, v, hxBoth.2, hyBoth.2⟩
  have hdistL : Distribution L x = Distribution L y :=
    hL hx hy hHxy hsharedL
  have hdistK : Distribution K x = Distribution K y :=
    hK hx hy hGxy hsharedK
  apply Set.ext
  intro c
  have hLctx :
      (c.1 ++ x ++ c.2 ∈ L) ↔
        (c.1 ++ y ++ c.2 ∈ L) := by
    have hc := Set.ext_iff.mp hdistL c
    simpa [Distribution] using hc
  have hKctx :
      (c.1 ++ x ++ c.2 ∈ K) ↔
        (c.1 ++ y ++ c.2 ∈ K) := by
    have hc := Set.ext_iff.mp hdistK c
    simpa [Distribution] using hc
  change
    ((c.1 ++ x ++ c.2 ∈ L) ∧
      (c.1 ++ x ++ c.2 ∈ K)) ↔
    ((c.1 ++ y ++ c.2 ∈ L) ∧
      (c.1 ++ y ++ c.2 ∈ K))
  constructor
  · rintro ⟨hxL, hxK⟩
    exact ⟨hLctx.mp hxL, hKctx.mp hxK⟩
  · rintro ⟨hyL, hyK⟩
    exact ⟨hLctx.mpr hyL, hKctx.mpr hyK⟩

/--
Substitutability part of Proposition 3.2(ii).

A language recognized by the second finite monoid is G-substitutable, so
regular filtering preserves fixed-h substitutability after passing to the
product typing.
-/
theorem fixedHSubstitutable_inter_recognized_product
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    (Acc : Set N)
    {L : Set (Word α)}
    (hL : FixedHSubstitutable H L) :
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G)
      (L ∩ RecognizedPreimage G Acc) := by
  exact
    fixedHSubstitutable_inter_product
      H G hL (recognizedPreimage_fixedHSubstitutable G Acc)

end V115FiniteInformationClosure

end TCS1
end LeanCfgProject
