import LeanCfgProject.TCS1.V115LocallyTrivialWindows

/-!
# TCS #1 v115: algebraic reduction for the forward local-window implication

The paper's Proposition 3.5 asserts that a locally trivial positive-image
semigroup S of size n forces equality of h-values for positive words with
identical (n,n) window summaries.

This file proves two exact bridges:
* the local-trivial identity e*t*e=e implies e*t*f=e*f when e and f
  are idempotents in the positive image and t*f also lies in the image;
* if all words of length n have idempotent h-image, local triviality implies
  the (n,n) fixed-window kernel refines h on nonempty words.

The algebraic lemma -- that an n-fold product of positive-image
elements is idempotent for n=|S| in a finite locally trivial semigroup --
is discharged in V115PositiveImageCardinal.  This intermediate module
isolates the boundary-erasure reduction without circular dependencies.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V115LocallyTrivialForwardReduction

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/--
Two idempotents e,f from the positive image satisfy e*t*f=e*f
when t*f is in the image.  This derives the three-factor absorption law
from the manuscript's definition e*s*e=e.
-/
theorem v115_locallyTrivial_twoIdempotentAbsorption
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    {e f t : M}
    (he : V115InPositiveImage H e)
    (hf : V115InPositiveImage H f)
    (htf : V115InPositiveImage H (t * f))
    (heidem : e * e = e)
    (hfidem : f * f = f) :
    e * t * f = e * f := by
  have hfef : f * e * f = f :=
    hlocal f e hf he hfidem
  have hetfe : e * (t * f) * e = e :=
    hlocal e (t * f) he htf heidem
  calc
    e * t * f = e * t * (f * e * f) := by rw [hfef]
    _ = (e * (t * f) * e) * f := by simp only [mul_assoc]
    _ = e * f := by rw [hetfe]

/-- Erasing a middle factor between positive idempotent boundary images. -/
theorem v115_locallyTrivial_boundaryErasure
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (p q m : Word α)
    (hpne : p ≠ [])
    (hqne : q ≠ [])
    (hpidem : H.h p * H.h p = H.h p)
    (hqidem : H.h q * H.h q = H.h q) :
    H.h (p ++ m ++ q) = H.h (p ++ q) := by
  have he : V115InPositiveImage H (H.h p) :=
    ⟨p, hpne, rfl⟩
  have hf : V115InPositiveImage H (H.h q) :=
    ⟨q, hqne, rfl⟩
  have hmqne : m ++ q ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_append, List.length_nil] at hlen
    have hqpos := List.length_pos_of_ne_nil hqne
    omega
  have htf :
      V115InPositiveImage H (H.h m * H.h q) :=
    ⟨m ++ q, hmqne, H.map_append m q⟩
  calc
    H.h (p ++ m ++ q) =
        H.h p * H.h m * H.h q := by
          rw [H.map_append (p ++ m) q, H.map_append p m]
    _ = H.h p * H.h q :=
      v115_locallyTrivial_twoIdempotentAbsorption
        H hlocal he hf htf hpidem hqidem
    _ = H.h (p ++ q) := (H.map_append p q).symm

/-- A boundary-erasure identity already suffices for window refinement. -/
theorem v115_windowRefinement_of_boundaryErasure
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat)
    (herase :
      ∀ p q m : Word α,
        p.length = k →
        q.length = l →
        H.h (p ++ m ++ q) = H.h (p ++ q)) :
    V115NonemptyKernelRefines
      (fixedWindowMonoidHom (α := α) k l)
      H := by
  intro x y _hx _hy heq
  have hsame :
      SameFixedWindowSummary k l x y :=
    fixedWindowMonoidHom_reflects (α := α) k l x y heq
  rcases hsame with ⟨_, hyx⟩ | ⟨_, _, p, q, m₁, m₂, hp, hq, hxdecomp, hydecomp⟩
  · rw [hyx]
  · rw [hxdecomp, hydecomp]
    calc
      H.h (p ++ m₁ ++ q) = H.h (p ++ q) :=
        herase p q m₁ hp hq
      _ = H.h (p ++ m₂ ++ q) :=
        (herase p q m₂ hp hq).symm

/--
The finite-algebraic content of the forward implication is precisely
eventual idempotence of n-letter positive products.

This implication uses no finiteness theorem beyond that explicitly passed
as the length-n idempotence premise.  Proving that premise for n=|S| is the
outstanding part of Proposition 3.5.
-/
theorem v115_windowRefinement_of_lengthIdempotence
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (n : Nat)
    (hn : 0 < n)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (hidempotent :
      ∀ p : Word α,
        p.length = n →
        H.h p * H.h p = H.h p) :
    V115NonemptyKernelRefines
      (fixedWindowMonoidHom (α := α) n n)
      H := by
  apply v115_windowRefinement_of_boundaryErasure H n n
  intro p q m hp hq
  have hpne : p ≠ [] := by
    intro hnil
    rw [hnil] at hp
    simp at hp
    omega
  have hqne : q ≠ [] := by
    intro hnil
    rw [hnil] at hq
    simp at hq
    omega
  exact v115_locallyTrivial_boundaryErasure
    H hlocal p q m hpne hqne
    (hidempotent p hp)
    (hidempotent q hq)

end V115LocallyTrivialForwardReduction

end TCS1
end LeanCfgProject
