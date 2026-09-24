import LeanCfgProject.TCS1.MarkedBoundaryNormalization

/-!
# TCS #1 v68: central-gap preservation on shortened reaching spines

The long-word proof of Lemma 7.1 must preserve more than the number of marked
leaves: every omitted sibling subtree has to remain in the single middle gap
between the first k and last l marked terminals.

A plain `ReachingSpine` is proposition-valued and therefore cannot be
inspected to compute positional data.  Instead we use a proposition-valued
refinement, `GapReachingSpine`, whose constructors carry the central-gap
invariant at the same time as the reaching-spine structure.

This module proves that repeated-label shortcutting preserves that refined
spine.  Hence cycle shortening cannot move an omitted sibling across one of
the marked boundary leaves.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundaryGapSemantic

variable {N : Type u}
variable {α : Type v}

/--
A reaching spine whose every omitted sibling occurs at the same global marked
leaf gap k.

`offset` is the number of marked leaves globally before the retained base,
and `marks` is the number of marked leaves carried by that base.
-/
inductive GapReachingSpine
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat) :
    N → N → Word α → Word α → List N → List Nat → Prop
  | hole
      {A : N} :
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A A [] [] [A] []
  | binaryLeft
      {A B C X : N}
      {left right z : Word α}
      {path : List N}
      {siblings : List Nat}
      (hbin : binaryRule A B C)
      (child :
        GapReachingSpine terminalRule binaryRule
          offset marks k
          B X left right path siblings)
      (sibling :
        UntypedDerives terminalRule binaryRule C z)
      (hgap : offset + marks = k) :
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A X left (right ++ z)
        (A :: path) (z.length :: siblings)
  | binaryRight
      {A B C X : N}
      {left right y : Word α}
      {path : List N}
      {siblings : List Nat}
      (hbin : binaryRule A B C)
      (sibling :
        UntypedDerives terminalRule binaryRule B y)
      (child :
        GapReachingSpine terminalRule binaryRule
          offset marks k
          C X left right path siblings)
      (hgap : offset = k) :
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A X (y ++ left) right
        (A :: path) (y.length :: siblings)

/-- Forget the gap certificate and recover the ordinary reaching spine. -/
theorem gapReachingSpine_toReachingSpine
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A X left right path siblings) :
    ReachingSpine terminalRule binaryRule
      A X left right path siblings := by
  induction spine with
  | hole =>
      exact ReachingSpine.hole
  | binaryLeft hbin child sibling hgap ih =>
      exact ReachingSpine.binaryLeft hbin ih sibling
  | binaryRight hbin sibling child hgap ih =>
      exact ReachingSpine.binaryRight hbin sibling ih

/--
A repetition-free suffix of a gap-certified reaching spine is again
gap-certified.
-/
theorem gapReachingSubspine_of_mem_of_nodup
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat)
    {A X Y : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A X left right path siblings)
    (hnodup : path.Nodup)
    (hmem : Y ∈ path) :
    ∃ left' right' path' siblings',
      GapReachingSpine terminalRule binaryRule
        offset marks k
        Y X left' right' path' siblings'
      ∧ path'.Nodup := by
  induction spine generalizing Y with
  | @hole A =>
      simp only [List.mem_singleton] at hmem
      subst Y
      exact
        ⟨[], [], [A], [],
          GapReachingSpine.hole,
          by simp⟩

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling hgap ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hYA | hYtail
      · subst Y
        exact
          ⟨left, right ++ z, A :: path,
            z.length :: siblings,
            GapReachingSpine.binaryLeft
              hbin child sibling hgap,
            (by rw [List.nodup_cons]; exact hnodup)⟩
      · exact ih hnodup.2 hYtail

  | @binaryRight A B C X left right y path siblings
      hbin sibling child hgap ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hYA | hYtail
      · subst Y
        exact
          ⟨y ++ left, right, A :: path,
            y.length :: siblings,
            GapReachingSpine.binaryRight
              hbin sibling child hgap,
            (by rw [List.nodup_cons]; exact hnodup)⟩
      · exact ih hnodup.2 hYtail

/--
Cycle shortening preserves the central-gap certificate.

This is the gap-aware counterpart of
`normalize_reachingSpine_to_nodup_unbounded`.
-/
theorem normalize_gapReachingSpine_to_nodup
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A X left right path siblings) :
    ∃ left' right' path' siblings',
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A X left' right' path' siblings'
      ∧ path'.Nodup := by
  induction spine with
  | @hole A =>
      exact
        ⟨[], [], [A], [],
          GapReachingSpine.hole,
          by simp⟩

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling hgap ih =>
      obtain ⟨left', right', path', siblings',
          child', hnodup⟩ := ih
      by_cases hmem : A ∈ path'
      · exact
          gapReachingSubspine_of_mem_of_nodup
            terminalRule binaryRule
            offset marks k
            child' hnodup hmem
      · exact
          ⟨left', right' ++ z, A :: path',
            z.length :: siblings',
            GapReachingSpine.binaryLeft
              hbin child' sibling hgap,
            (by
              rw [List.nodup_cons]
              exact ⟨hmem, hnodup⟩)⟩

  | @binaryRight A B C X left right y path siblings
      hbin sibling child hgap ih =>
      obtain ⟨left', right', path', siblings',
          child', hnodup⟩ := ih
      by_cases hmem : A ∈ path'
      · exact
          gapReachingSubspine_of_mem_of_nodup
            terminalRule binaryRule
            offset marks k
            child' hnodup hmem
      · exact
          ⟨y ++ left', right', A :: path',
            y.length :: siblings',
            GapReachingSpine.binaryRight
              hbin sibling child' hgap,
            (by
              rw [List.nodup_cons]
              exact ⟨hmem, hnodup⟩)⟩

/--
A gap-certified reaching spine has the same path/sibling cardinality identity
as an ordinary reaching spine.
-/
theorem gapReachingSpine_siblings_length_add_one_eq_path
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A X left right path siblings) :
    siblings.length + 1 = path.length := by
  exact
    reachingSpine_siblings_length_add_one_eq_path
      terminalRule binaryRule
      (gapReachingSpine_toReachingSpine
        terminalRule binaryRule
        offset marks k spine)

end MarkedBoundaryGapSemantic

end TCS1
end LeanCfgProject
