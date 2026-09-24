import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v77: finite and singleton fixed-h facts

This module formalizes two v77 clarifications.

* Every singleton language is fixed-h substitutable for every fixed typing h.
  This is the representation-size obstruction used in Section 6.
* For every fixed finite typing over a nonempty alphabet there is a finite
  language that is not fixed-h substitutable.  This is the finite-language
  counter used to separate each fixed slice from Gold's superfinite setting.

The second statement is proved by first obtaining two distinct nonempty words
with the same finite h-type by pigeonhole, then using the paper's three-word
counter {x,y,rx}.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FixedHFiniteObstructions

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/--
Every singleton language is fixed-h substitutable, independently of the
chosen finite monoid homomorphism.
-/
theorem singleton_fixedHSubstitutable
    (H : FixedFiniteMonoidHom α M)
    (w : Word α) :
    FixedHSubstitutable H ({w} : Set (Word α)) := by
  intro x y _hx _hy _htype hshared
  rcases hshared with ⟨u, v, hx, hy⟩
  have hxw : u ++ x ++ v = w := by
    simpa only [Set.mem_singleton_iff] using hx
  have hyw : u ++ y ++ v = w := by
    simpa only [Set.mem_singleton_iff] using hy
  have hctx : u ++ x ++ v = u ++ y ++ v :=
    hxw.trans hyw.symm
  have hctx' : u ++ (x ++ v) = u ++ (y ++ v) := by
    simpa [List.append_assoc] using hctx
  have hxyv : x ++ v = y ++ v :=
    List.append_cancel_left hctx'
  have hxy : x = y :=
    List.append_cancel_right hxyv
  subst y
  rfl

/--
Because the word monoid over a nonempty alphabet is infinite while M is
finite, every fixed typing identifies two distinct nonempty words.
-/
theorem exists_distinct_nonempty_same_fixedH_type
    [Nonempty α]
    (H : FixedFiniteMonoidHom α M) :
    ∃ x y : Word α,
      x ≠ [] ∧
      y ≠ [] ∧
      x ≠ y ∧
      H.h x = H.h y := by
  classical
  let a : α := Classical.choice (inferInstance : Nonempty α)
  let f : Nat → M :=
    fun n => H.h (List.replicate (n + 1) a)
  obtain ⟨n, m, hnm, htype⟩ :=
    Finite.exists_ne_map_eq_of_infinite f
  refine
    ⟨List.replicate (n + 1) a,
      List.replicate (m + 1) a,
      ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro hwords
    have hlen := congrArg List.length hwords
    simp at hlen
    exact hnm hlen
  · simpa [f] using htype

/-- The three-word finite counter used in the v77 Section 3 argument. -/
def collisionCounterLanguage
    (x y r : Word α) :
    Set (Word α) :=
  {x, y, r ++ x}

/--
If x and y are distinct nonempty words of the same h-type and r is longer
than both, the finite language {x,y,rx} is not fixed-h substitutable.
-/
theorem collisionCounter_not_fixedHSubstitutable
    (H : FixedFiniteMonoidHom α M)
    {x y r : Word α}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hxyne : x ≠ y)
    (htype : H.h x = H.h y)
    (hr :
      max x.length y.length < r.length) :
    ¬ FixedHSubstitutable
        H
        (collisionCounterLanguage x y r) := by
  intro hsub
  have hshared :
      HaveSharedContext
        (collisionCounterLanguage x y r)
        x y := by
    refine ⟨[], [], ?_, ?_⟩
    · simp [collisionCounterLanguage]
    · simp [collisionCounterLanguage]
  have hdist :
      Distribution
          (collisionCounterLanguage x y r) x =
        Distribution
          (collisionCounterLanguage x y r) y :=
    hsub hxne hyne htype hshared
  have hxctx :
      (r, []) ∈
        Distribution
          (collisionCounterLanguage x y r) x := by
    simp [Distribution, collisionCounterLanguage]
  have hyctx :
      (r, []) ∈
        Distribution
          (collisionCounterLanguage x y r) y := by
    rw [← hdist]
    exact hxctx

  have hxmax :
      x.length ≤ max x.length y.length :=
    Nat.le_max_left _ _
  have hymax :
      y.length ≤ max x.length y.length :=
    Nat.le_max_right _ _
  have hrx : x.length < r.length :=
    lt_of_le_of_lt hxmax hr
  have hry : y.length < r.length :=
    lt_of_le_of_lt hymax hr
  have hrpos : 0 < r.length :=
    lt_of_le_of_lt (Nat.zero_le _) hrx

  have hnotx : r ++ y ≠ x := by
    intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_append] at hlen
    omega
  have hnoty : r ++ y ≠ y := by
    intro heq
    have hlen := congrArg List.length heq
    simp only [List.length_append] at hlen
    omega
  have hnotrx : r ++ y ≠ r ++ x := by
    intro heq
    have hyx : y = x :=
      List.append_cancel_left heq
    exact hxyne hyx.symm

  have hnot :
      r ++ y ∉ collisionCounterLanguage x y r := by
    intro hmem
    simp only
      [collisionCounterLanguage,
       Set.mem_insert_iff,
       Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h
    · exact hnotx h
    · exact hnoty h
    · exact hnotrx h

  apply hnot
  simpa [Distribution] using hyctx

/--
Paper-facing class-level consequence needed in v77: for every fixed finite h
over a nonempty alphabet, some finite language lies outside the fixed-h slice.
-/
theorem exists_finite_language_not_fixedHSubstitutable
    [Nonempty α]
    (H : FixedFiniteMonoidHom α M) :
    ∃ L : Set (Word α),
      L.Finite ∧
      ¬ FixedHSubstitutable H L := by
  classical
  obtain ⟨x, y, hxne, hyne, hxyne, htype⟩ :=
    exists_distinct_nonempty_same_fixedH_type H
  let a : α := Classical.choice (inferInstance : Nonempty α)
  let r : Word α :=
    List.replicate
      (max x.length y.length + 1) a
  have hr :
      max x.length y.length < r.length := by
    simp [r]
  refine
    ⟨collisionCounterLanguage x y r, ?_, ?_⟩
  · simp [collisionCounterLanguage]
  · exact
      collisionCounter_not_fixedHSubstitutable
        H hxne hyne hxyne htype hr

end FixedHFiniteObstructions

end TCS1
end LeanCfgProject
