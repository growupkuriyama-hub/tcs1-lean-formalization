import LeanCfgProject.TCS1.V115LocallyTrivialForwardReduction

/-!
# TCS #1 v115: the positive-image idempotents form a two-sided ideal

This module isolates the first elementary step in Pin, Proposition XI.4.17.
For the positive-image semigroup S = h(Sigma+), the locally-trivial law
e*s*e=e implies that any product in S containing an idempotent factor is
itself idempotent.

Importantly, this file does NOT assume any idempotent-factor existence
lemma.  Deriving an idempotent factor in a product of |S| generators is
the separate finite-semigroup combinatorial step still to be checked.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V115PositiveIdempotentIdeal
variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Positive image is closed under multiplication. -/
theorem v115_positiveImage_mul
    (H : FixedFiniteMonoidHom α M)
    {s t : M}
    (hs : V115InPositiveImage H s)
    (ht : V115InPositiveImage H t) :
    V115InPositiveImage H (s * t) := by
  rcases hs with ⟨p, hpne, rfl⟩
  rcases ht with ⟨q, hqne, rfl⟩
  refine ⟨p ++ q, ?_, H.map_append p q⟩
  intro hnil
  have hpos : 0 < p.length :=
    List.length_pos_of_ne_nil hpne
  have hlen := congrArg List.length hnil
  simp only [List.length_append, List.length_nil] at hlen
  omega

/-- Multiplying a positive idempotent on the right preserves idempotence. -/
theorem v115_positiveImage_idempotent_right
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    {e t : M}
    (he : V115InPositiveImage H e)
    (ht : V115InPositiveImage H t)
    (he2 : e * e = e) :
    (e * t) * (e * t) = e * t := by
  calc
    (e * t) * (e * t) = (e * t * e) * t := by simp only [mul_assoc]
    _ = e * t := by rw [hlocal e t he ht he2]

/-- Multiplying a positive idempotent on the left preserves idempotence. -/
theorem v115_positiveImage_idempotent_left
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    {e t : M}
    (he : V115InPositiveImage H e)
    (ht : V115InPositiveImage H t)
    (he2 : e * e = e) :
    (t * e) * (t * e) = t * e := by
  calc
    (t * e) * (t * e) = t * (e * t * e) := by simp only [mul_assoc]
    _ = t * e := by rw [hlocal e t he ht he2]

/--
The idempotents in S are a two-sided ideal: the middle idempotent
forces the whole positive sandwich to be idempotent.
-/
theorem v115_positiveImage_idempotent_sandwich
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    {e t u : M}
    (he : V115InPositiveImage H e)
    (ht : V115InPositiveImage H t)
    (hu : V115InPositiveImage H u)
    (he2 : e * e = e) :
    (t * e * u) * (t * e * u) = t * e * u := by
  have htu : V115InPositiveImage H (u * t) :=
    v115_positiveImage_mul H hu ht
  calc
    (t * e * u) * (t * e * u) =
        t * (e * (u * t) * e) * u := by simp only [mul_assoc]
    _ = t * e * u := by
      rw [hlocal e (u * t) he htu he2]

/--
If a nonempty internal factor has idempotent h-image then the image of
the entire word is idempotent, even with empty left/right contexts.
-/
theorem v115_idempotent_factor_implies_word_idempotent
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (p r q : Word α)
    (hrne : r ≠ [])
    (hr2 : H.h r * H.h r = H.h r) :
    H.h (p ++ r ++ q) * H.h (p ++ r ++ q) =
      H.h (p ++ r ++ q) := by
  have he : V115InPositiveImage H (H.h r) :=
    ⟨r, hrne, rfl⟩
  by_cases hp : p = []
  · subst p
    by_cases hq : q = []
    · subst q
      simpa using hr2
    · have hqpos : V115InPositiveImage H (H.h q) :=
        ⟨q, hq, rfl⟩
      simpa [H.map_append] using
        v115_positiveImage_idempotent_right
          H hlocal he hqpos hr2
  · have hppos : V115InPositiveImage H (H.h p) :=
      ⟨p, hp, rfl⟩
    by_cases hq : q = []
    · subst q
      simpa [H.map_append] using
        v115_positiveImage_idempotent_left
          H hlocal he hppos hr2
    · have hqpos : V115InPositiveImage H (H.h q) :=
        ⟨q, hq, rfl⟩
      simpa [H.map_append, mul_assoc] using
        v115_positiveImage_idempotent_sandwich
          H hlocal he hppos hqpos hr2

end V115PositiveIdempotentIdeal
end TCS1
end LeanCfgProject
