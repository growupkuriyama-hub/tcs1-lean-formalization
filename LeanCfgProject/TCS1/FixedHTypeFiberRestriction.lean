import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v83: restriction to fixed-h type fibres

This module verifies the new v83 lemma used by the ordinary-thickness lower
bound: a fixed-h substitutable language remains fixed-h substitutable after
intersection with an arbitrary union of h-fibres.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

/--
Restriction to any selected set of fixed-h types preserves
fixed-h substitutability.

Paper-facing v83 statement:
if L is ~_h-substitutable and F is a subset of the finite monoid, then
L ∩ h^{-1}(F) is again ~_h-substitutable.
-/
theorem fixedHSubstitutable_inter_recognizedPreimage
    {α : Type u}
    {M : Type v} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    {L : Set (Word α)}
    (F : Set M)
    (hsub : FixedHSubstitutable H L) :
    FixedHSubstitutable H (L ∩ RecognizedPreimage H F) := by
  intro x y hx hy hxy hshared
  have hsharedL : HaveSharedContext L x y := by
    rcases hshared with ⟨u, v, hux, huy⟩
    exact ⟨u, v, hux.1, huy.1⟩
  have hdist : Distribution L x = Distribution L y :=
    hsub hx hy hxy hsharedL
  apply Set.ext
  intro c
  have hL :
      (c.1 ++ x ++ c.2 ∈ L) ↔
        (c.1 ++ y ++ c.2 ∈ L) := by
    have hc :=
      Set.ext_iff.mp hdist c
    simpa [Distribution] using hc
  have htype :
      H.h (c.1 ++ x ++ c.2) =
        H.h (c.1 ++ y ++ c.2) :=
    context_image_eq H hxy c.1 c.2
  have htype' :
      H.h (c.1 ++ (x ++ c.2)) =
        H.h (c.1 ++ (y ++ c.2)) := by
    simpa only [List.append_assoc] using htype
  change
    ((c.1 ++ x ++ c.2 ∈ L) ∧
      H.h (c.1 ++ (x ++ c.2)) ∈ F) ↔
    ((c.1 ++ y ++ c.2 ∈ L) ∧
      H.h (c.1 ++ (y ++ c.2)) ∈ F)
  constructor
  · rintro ⟨hxL, hxF⟩
    refine ⟨hL.mp hxL, ?_⟩
    rw [← htype']
    exact hxF
  · rintro ⟨hyL, hyF⟩
    refine ⟨hL.mpr hyL, ?_⟩
    rw [htype']
    exact hyF

end TCS1
end LeanCfgProject
