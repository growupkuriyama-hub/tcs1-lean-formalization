import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v77: fixed-word quotient closure

This module formalizes the fixed-word right-quotient lemma used in the
boundary section of the manuscript.  For a fixed word z, a common context
(u,v) in L/z becomes (u,vz) in L; the same translation transfers every
distributional context back and forth.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FixedWordQuotient

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Right quotient by one fixed word. -/
def FixedRightQuotient
    (L : Set (Word α))
    (z : Word α) :
    Set (Word α) :=
  { w | w ++ z ∈ L }

/--
Lemma (fixed-word quotient): fixed-h substitutability is closed under right
quotient by one fixed word.
-/
theorem fixedHSubstitutable_fixedRightQuotient
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (z : Word α)
    (hsub : FixedHSubstitutable H L) :
    FixedHSubstitutable H (FixedRightQuotient L z) := by
  intro x y hx hy htype hsharedQ
  rcases hsharedQ with
    ⟨u, v, hsharedXQ, hsharedYQ⟩
  have hsharedL : HaveSharedContext L x y := by
    refine ⟨u, v ++ z, ?_, ?_⟩
    · simpa [FixedRightQuotient, List.append_assoc] using hsharedXQ
    · simpa [FixedRightQuotient, List.append_assoc] using hsharedYQ
  have hdistL :
      Distribution L x = Distribution L y :=
    hsub hx hy htype hsharedL
  apply Set.ext
  rintro ⟨s, t⟩
  constructor
  · intro hctxXQ
    have hctxXL :
        (s, t ++ z) ∈ Distribution L x := by
      simpa [Distribution, FixedRightQuotient, List.append_assoc]
        using hctxXQ
    have hctxYL :
        (s, t ++ z) ∈ Distribution L y := by
      rw [← hdistL]
      exact hctxXL
    simpa [Distribution, FixedRightQuotient, List.append_assoc]
      using hctxYL
  · intro hctxYQ
    have hctxYL :
        (s, t ++ z) ∈ Distribution L y := by
      simpa [Distribution, FixedRightQuotient, List.append_assoc]
        using hctxYQ
    have hctxXL :
        (s, t ++ z) ∈ Distribution L x := by
      rw [hdistL]
      exact hctxYL
    simpa [Distribution, FixedRightQuotient, List.append_assoc]
      using hctxXL

end FixedWordQuotient

end TCS1
end LeanCfgProject
