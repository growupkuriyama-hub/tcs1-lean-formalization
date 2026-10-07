import LeanCfgProject.TCS1.LinearRegularIntersection
import LeanCfgProject.TCS1.RegularRecognition
import LeanCfgProject.TCS1.V121FiniteInformationClosure

/-!
# TCS #1 v126: unnumbered linear regular-filter closure

The current manuscript contains the displayed, unnumbered implication

  L in Clin_H, Q = G^{-1}(F)  ==>  L ∩ Q in Clin_{H×G}.

This is easy to miss in an audit that only counts theorem environments.
The two ingredients were already verified separately:

* finite raw-linear presentations are closed under intersection with a DFA;
* fixed-H substitutability is preserved by the product typing when the second
  language is recognized by a finite monoid.

This file packages the exact combined claim.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w m

section V126LinearRegularFilterClosure

variable {α : Type v}
variable {M : Type m} {N : Type}
variable [Monoid M] [Fintype M]
variable [Monoid N] [Fintype N]

/-- Machine-checked version of the manuscript's unnumbered linear
regular-filter closure statement. -/
theorem rawLinear_fixedH_inter_recognized_product
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α N)
    (Acc : Set N)
    {L : Set (Word α)}
    (hlin :
      RawLinearInitialRepresentable.{u, v, w} L)
    (hsub : FixedHSubstitutable H L) :
    RawLinearInitialRepresentable.{u, v, w}
      (L ∩ RecognizedPreimage G Acc)
    ∧
    FixedHSubstitutable
      (productTyping H G)
      (L ∩ RecognizedPreimage G Acc) := by
  constructor
  · have hlin' :=
      rawLinearInitialRepresentable_inter_dfa
        (D := monoidRecognitionDFA G Acc)
        hlin
    rw [monoidRecognitionDFA_accepts_eq G Acc] at hlin'
    exact hlin'
  · exact
      fixedHSubstitutable_inter_recognized_product
        H G Acc hsub

end V126LinearRegularFilterClosure

end TCS1
end LeanCfgProject
