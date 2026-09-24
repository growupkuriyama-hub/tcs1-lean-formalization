import LeanCfgProject.TCS1.FixedWindowClassicalSubstitutability

/-!
# TCS #1 v78: fixed-window counterexample criterion

The manuscript repeatedly uses the same semantic pattern: two nonempty factors
have the same fixed-window summary and a common positive context, but their
full distributions differ.  Such a pair contradicts fixed-window
substitutability.

This file packages that argument once, through the concrete finite-monoid
summary h_{k,l}.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section FixedWindowCounterexampleCriterion

variable {α : Type u} [Fintype α]

/--
Paper-facing fixed-window counterexample criterion.

If two nonempty words have the same (k,l) summary, share a context in L, and
have unequal distributions, then L is not (k,l)-substitutable.
-/
theorem not_fixedWindowSubstitutable_of_bad_pair
    (k l : Nat)
    (L : Set (Word α))
    (x y : Word α)
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hsame :
      SameFixedWindowSummary k l x y)
    (hshared :
      HaveSharedContext L x y)
    (hdist :
      Distribution L x ≠
        Distribution L y) :
    ¬ FixedWindowSubstitutable k l L := by
  intro hwin
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom
          (α := α) k l)
        L :=
    fixedHSubstitutable_of_fixedWindowSubstitutable
      k l L hwin
  have htype :
      (fixedWindowMonoidHom
          (α := α) k l).h x =
        (fixedWindowMonoidHom
          (α := α) k l).h y :=
    fixedWindowMonoidHom_respects
      (α := α) k l x y hsame
  exact
    hdist
      (hsub hxne hyne htype hshared)

/--
Convenient form when a specific context distinguishes the two distributions.
-/
theorem not_fixedWindowSubstitutable_of_distinguishing_context
    (k l : Nat)
    (L : Set (Word α))
    (x y : Word α)
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hsame :
      SameFixedWindowSummary k l x y)
    (hshared :
      HaveSharedContext L x y)
    (u v : Word α)
    (hxctx :
      u ++ x ++ v ∈ L)
    (hyctx :
      u ++ y ++ v ∉ L) :
    ¬ FixedWindowSubstitutable k l L := by
  apply
    not_fixedWindowSubstitutable_of_bad_pair
      k l L x y hxne hyne hsame hshared
  intro hdist
  have hxD :
      (u, v) ∈ Distribution L x := by
    exact hxctx
  have hyD :
      (u, v) ∈ Distribution L y := by
    rw [← hdist]
    exact hxD
  exact hyctx hyD

end FixedWindowCounterexampleCriterion

end TCS1
end LeanCfgProject
