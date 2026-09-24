import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v79: fixed-h compatibility with Gold's superfinite obstruction

Immediately after the main theorem, the manuscript explains why the fixed-h
target class does not conflict with Gold's standard superfinite negative
result.  Over every nonempty finite alphabet and every fixed finite typing h,
one can find two distinct nonempty words with the same h-value and build a
three-word finite language that is not fixed-h substitutable.

This module formalizes that manuscript paragraph.

The proof has two layers:
* a generic three-word obstruction from one same-type collision; and
* a finite-pigeonhole construction of such a collision from the infinitely
  many positive powers of one alphabet symbol.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section GoldCompatibilityFiniteObstruction

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]

/-- The manuscript's finite witness language {x, y, r x}. -/
def goldThreeWordSample
    (x y r : Word α) :
    Finset (Word α) :=
  {x, y, r ++ x}

/--
If x and y are distinct nonempty same-type words and r is longer than each,
then the finite language {x,y,rx} is not fixed-h substitutable.

The shared empty context compares x and y, while the context (r,epsilon)
belongs to x but not to y.
-/
theorem goldThreeWordSample_not_fixedH
    (H : FixedFiniteMonoidHom α M)
    {x y r : Word α}
    (hx : x ≠ [])
    (hy : y ≠ [])
    (hxy : x ≠ y)
    (htype : H.h x = H.h y)
    (hrx : x.length < r.length)
    (hry : y.length < r.length) :
    ¬ FixedHSubstitutable H
        (↑(goldThreeWordSample x y r) :
          Set (Word α)) := by
  intro hsub
  let L : Set (Word α) :=
    ↑(goldThreeWordSample x y r)

  have hshared :
      HaveSharedContext L x y := by
    refine ⟨[], [], ?_, ?_⟩
    · simp [L, goldThreeWordSample]
    · simp [L, goldThreeWordSample]

  have hdist :
      Distribution L x = Distribution L y :=
    hsub hx hy htype hshared

  have hrxContext :
      (r, ([] : Word α)) ∈ Distribution L x := by
    simp [Distribution, L, goldThreeWordSample]

  have hryContext :
      (r, ([] : Word α)) ∈ Distribution L y := by
    rw [← hdist]
    exact hrxContext

  have hryMem :
      r ++ y ∈ goldThreeWordSample x y r := by
    simpa [Distribution, L] using hryContext

  have hryNotMem :
      r ++ y ∉ goldThreeWordSample x y r := by
    intro hmem
    simp only [goldThreeWordSample, Finset.mem_insert,
      Finset.mem_singleton] at hmem
    rcases hmem with hEqX | hEqY | hEqRX
    · have hlen := congrArg List.length hEqX
      simp only [List.length_append] at hlen
      omega
    · have hlen := congrArg List.length hEqY
      simp only [List.length_append] at hlen
      omega
    · have hyx : y = x :=
        List.append_cancel_left hEqRX
      exact hxy hyx.symm

  exact hryNotMem hryMem

/--
For every fixed finite typing over a nonempty alphabet, some finite language
is outside the corresponding fixed-h substitutable class.

This is the formal version of the compatibility paragraph following the main
theorem: the fixed-h class is not superfinite, so Gold's classical
superfinite obstruction does not contradict the positive result.
-/
theorem fixedH_omits_some_finite_language
    [Nonempty α]
    (H : FixedFiniteMonoidHom α M) :
    ∃ K : Finset (Word α),
      ¬ FixedHSubstitutable H
          (↑K : Set (Word α)) := by
  classical
  let a : α :=
    Classical.choice (inferInstance : Nonempty α)
  let f : Nat → M :=
    fun n =>
      H.h (List.replicate (n + 1) a)

  obtain ⟨n, m, hnm, hsame⟩ :=
    Finite.exists_ne_map_eq_of_infinite f

  let x : Word α :=
    List.replicate (n + 1) a
  let y : Word α :=
    List.replicate (m + 1) a

  have hx : x ≠ [] := by
    simp [x]
  have hy : y ≠ [] := by
    simp [y]
  have hxy : x ≠ y := by
    intro h
    have hlen :=
      congrArg List.length h
    simp [x, y] at hlen
    omega
  have htype :
      H.h x = H.h y := by
    simpa [f, x, y] using hsame

  let r : Word α :=
    List.replicate
      (max x.length y.length + 1)
      a

  have hrx : x.length < r.length := by
    simp [r]
  have hry : y.length < r.length := by
    simp [r]

  refine
    ⟨goldThreeWordSample x y r, ?_⟩
  exact
    goldThreeWordSample_not_fixedH
      H hx hy hxy htype hrx hry

end GoldCompatibilityFiniteObstruction

end TCS1
end LeanCfgProject
