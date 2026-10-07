import Mathlib.Algebra.Group.Defs

/-!
# TCS #1 v126: elementary locally-trivial semigroup core

The current manuscript defines a semigroup S to be locally trivial by

  e * t * e = e

for every idempotent e and every t.  Its proof of the fixed-window criterion
then uses the consequence

  e * t * f = e * f

for idempotents e,f.

This file proves that consequence directly from the manuscript definition.
Thus this step is no longer part of the external Pin dependency.  The
genuinely external finite-semigroup input in the manuscript is separated from
this elementary calculation.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section V126LocallyTrivialCore

variable {S : Type u} [Semigroup S]

/-- The manuscript's definition of local triviality for a semigroup. -/
def SemigroupLocallyTrivial : Prop :=
  ∀ e : S, e * e = e → ∀ t : S, e * t * e = e

/-- A locally trivial semigroup collapses everything between two idempotents:
e t f = e f.  This is the exact identity used in the v126 proof. -/
theorem locallyTrivial_between_idempotents
    (hlt : SemigroupLocallyTrivial (S := S))
    {e f t : S}
    (he : e * e = e)
    (hf : f * f = f) :
    e * t * f = e * f := by
  have hfef : f * e * f = f :=
    hlt f hf e
  have hete : e * (t * f) * e = e :=
    hlt e he (t * f)
  calc
    e * t * f = e * t * (f * e * f) := by rw [hfef]
    _ = (e * (t * f) * e) * f := by simp only [mul_assoc]
    _ = e * f := by rw [hete]

/-- Paper-shaped sandwich calculation used after the two idempotent
factorizations of h(p) and h(q). -/
theorem locallyTrivial_double_sandwich
    (hlt : SemigroupLocallyTrivial (S := S))
    {a b c d e f s : S}
    (he : e * e = e)
    (hf : f * f = f) :
    a * e * (b * s * c) * f * d =
      a * e * f * d := by
  have hmid :
      e * (b * s * c) * f = e * f :=
    locallyTrivial_between_idempotents
      (S := S) hlt he hf
  calc
    a * e * (b * s * c) * f * d
        = a * (e * (b * s * c) * f) * d := by
            simp only [mul_assoc]
    _ = a * (e * f) * d := by rw [hmid]
    _ = a * e * f * d := by simp only [mul_assoc]

end V126LocallyTrivialCore

end TCS1
end LeanCfgProject
