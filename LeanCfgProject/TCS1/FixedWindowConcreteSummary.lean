import LeanCfgProject.TCS1.FixedWindowBoundaryMarking
import LeanCfgProject.TCS1.FixedWindowSummarySemantic

/-!
# TCS #1 v68: concrete finite fixed-window summary states

This module begins the representation-level formalization of Proposition 3.2.
It gives a genuinely finite tagged state space for the short/long
prefix--suffix summary and proves that equality of these concrete states is
exactly `SameFixedWindowSummary`.

The monoid multiplication on the image of this summary is added in the next
layer.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section FixedWindowConcreteSummary

variable {α : Type u}

/-- Short states remember the complete word together with its length index. -/
abbrev FixedWindowShortState
    (α : Type u) (k l : Nat) :=
  Σ n : Fin (fixedWindowThreshold k l), List.Vector α n

/-- Long states remember exactly a length-k prefix and length-l suffix. -/
abbrev FixedWindowLongState
    (α : Type u) (k l : Nat) :=
  List.Vector α k × List.Vector α l

/-- Tagged concrete carrier before restricting to the image of the summary. -/
abbrev FixedWindowRawState
    (α : Type u) (k l : Nat) :=
  Sum
    (FixedWindowShortState α k l)
    (FixedWindowLongState α k l)

/-- The fixed-window prefix packaged as a length-indexed vector. -/
def fixedWindowPrefixVector
    (w : Word α) (k l : Nat)
    (hfit : k + l ≤ w.length) :
    List.Vector α k :=
  ⟨w.take k, fixedWindow_prefix_length w k l hfit⟩

/-- The fixed-window suffix packaged as a length-indexed vector. -/
def fixedWindowSuffixVector
    (w : Word α) (k l : Nat)
    (hfit : k + l ≤ w.length) :
    List.Vector α l :=
  ⟨w.drop (w.length - l),
    fixedWindow_suffix_length w k l hfit⟩

/--
Concrete tagged summary from Proposition 3.2.

Short words are stored literally; long words are stored by their fixed
prefix and suffix.
-/
def fixedWindowRawSummary
    (k l : Nat) (w : Word α) :
    FixedWindowRawState α k l :=
  if hshort : w.length < fixedWindowThreshold k l then
    Sum.inl
      ⟨⟨w.length, hshort⟩,
        (⟨w, rfl⟩ : List.Vector α w.length)⟩
  else
    have hcut :
        fixedWindowThreshold k l ≤ w.length :=
      Nat.le_of_not_gt hshort
    have hfit : k + l ≤ w.length := by
      have hsum :
          k + l ≤ fixedWindowThreshold k l := by
        unfold fixedWindowThreshold
        omega
      exact le_trans hsum hcut
    Sum.inr
      (fixedWindowPrefixVector w k l hfit,
       fixedWindowSuffixVector w k l hfit)

/-- Read the literal word out of a short state, when present. -/
def fixedWindowShortWord? {k l : Nat} :
    FixedWindowRawState α k l → Option (Word α)
  | Sum.inl s => some s.2.toList
  | Sum.inr _ => none

/-- Read the prefix out of a long state, when present. -/
def fixedWindowPrefix? {k l : Nat} :
    FixedWindowRawState α k l → Option (Word α)
  | Sum.inl _ => none
  | Sum.inr z => some z.1.toList

/-- Read the suffix out of a long state, when present. -/
def fixedWindowSuffix? {k l : Nat} :
    FixedWindowRawState α k l → Option (Word α)
  | Sum.inl _ => none
  | Sum.inr z => some z.2.toList

theorem fixedWindowRawSummary_shortWord
    {k l : Nat} {w : Word α}
    (hshort : w.length < fixedWindowThreshold k l) :
    fixedWindowShortWord?
        (fixedWindowRawSummary k l w) =
      some w := by
  simp [fixedWindowRawSummary, hshort, fixedWindowShortWord?]

theorem fixedWindowRawSummary_longPrefix
    {k l : Nat} {w : Word α}
    (hcut : fixedWindowThreshold k l ≤ w.length) :
    fixedWindowPrefix?
        (fixedWindowRawSummary k l w) =
      some (w.take k) := by
  have hnot :
      ¬ w.length < fixedWindowThreshold k l :=
    not_lt_of_ge hcut
  simp [fixedWindowRawSummary, hnot,
    fixedWindowPrefix?, fixedWindowPrefixVector]

theorem fixedWindowRawSummary_longSuffix
    {k l : Nat} {w : Word α}
    (hcut : fixedWindowThreshold k l ≤ w.length) :
    fixedWindowSuffix?
        (fixedWindowRawSummary k l w) =
      some (w.drop (w.length - l)) := by
  have hnot :
      ¬ w.length < fixedWindowThreshold k l :=
    not_lt_of_ge hcut
  simp [fixedWindowRawSummary, hnot,
    fixedWindowSuffix?, fixedWindowSuffixVector]

/-- Equality of concrete summaries implies equality of the semantic summaries. -/
theorem sameFixedWindowSummary_of_rawSummary_eq
    {k l : Nat} {x y : Word α}
    (heq :
      fixedWindowRawSummary k l x =
        fixedWindowRawSummary k l y) :
    SameFixedWindowSummary k l x y := by
  by_cases hx :
      x.length < fixedWindowThreshold k l
  · have hxWord :=
      fixedWindowRawSummary_shortWord
        (α := α) hx
    by_cases hy :
        y.length < fixedWindowThreshold k l
    · have hyWord :=
        fixedWindowRawSummary_shortWord
          (α := α) hy
      have hopen :
          (some x : Option (Word α)) = some y := by
        calc
          some x =
              fixedWindowShortWord?
                (fixedWindowRawSummary k l x) := hxWord.symm
          _ =
              fixedWindowShortWord?
                (fixedWindowRawSummary k l y) := by rw [heq]
          _ = some y := hyWord
      have hxy : x = y := Option.some.inj hopen
      exact Or.inl ⟨hx, hxy.symm⟩
    · have hycut :
          fixedWindowThreshold k l ≤ y.length :=
        Nat.le_of_not_gt hy
      have hxSome :
          fixedWindowShortWord?
              (fixedWindowRawSummary k l x) =
            some x :=
        hxWord
      have hyNone :
          fixedWindowShortWord?
              (fixedWindowRawSummary k l y) =
            none := by
        have hnot :
            ¬ y.length < fixedWindowThreshold k l := hy
        simp [fixedWindowRawSummary, hnot,
          fixedWindowShortWord?]
      have : (some x : Option (Word α)) = none := by
        calc
          some x =
              fixedWindowShortWord?
                (fixedWindowRawSummary k l x) := hxSome.symm
          _ =
              fixedWindowShortWord?
                (fixedWindowRawSummary k l y) := by rw [heq]
          _ = none := hyNone
      cases this
  · have hxcut :
        fixedWindowThreshold k l ≤ x.length :=
      Nat.le_of_not_gt hx
    have hsum :
        k + l ≤ fixedWindowThreshold k l := by
      unfold fixedWindowThreshold
      omega
    have hfitx : k + l ≤ x.length :=
      le_trans hsum hxcut
    by_cases hy :
        y.length < fixedWindowThreshold k l
    · have hyWord :=
        fixedWindowRawSummary_shortWord
          (α := α) hy
      have hxNone :
          fixedWindowShortWord?
              (fixedWindowRawSummary k l x) =
            none := by
        simp [fixedWindowRawSummary, hx,
          fixedWindowShortWord?]
      have : (none : Option (Word α)) = some y := by
        calc
          none =
              fixedWindowShortWord?
                (fixedWindowRawSummary k l x) := hxNone.symm
          _ =
              fixedWindowShortWord?
                (fixedWindowRawSummary k l y) := by rw [heq]
          _ = some y := hyWord
      cases this
    · have hycut :
          fixedWindowThreshold k l ≤ y.length :=
        Nat.le_of_not_gt hy
      have hfity : k + l ≤ y.length :=
        le_trans hsum hycut
      have hpEqSome :
          some (x.take k) = some (y.take k) := by
        calc
          some (x.take k) =
              fixedWindowPrefix?
                (fixedWindowRawSummary k l x) :=
            (fixedWindowRawSummary_longPrefix
              (α := α) hxcut).symm
          _ =
              fixedWindowPrefix?
                (fixedWindowRawSummary k l y) := by rw [heq]
          _ = some (y.take k) :=
            fixedWindowRawSummary_longPrefix
              (α := α) hycut
      have hqEqSome :
          some (x.drop (x.length - l)) =
            some (y.drop (y.length - l)) := by
        calc
          some (x.drop (x.length - l)) =
              fixedWindowSuffix?
                (fixedWindowRawSummary k l x) :=
            (fixedWindowRawSummary_longSuffix
              (α := α) hxcut).symm
          _ =
              fixedWindowSuffix?
                (fixedWindowRawSummary k l y) := by rw [heq]
          _ = some (y.drop (y.length - l)) :=
            fixedWindowRawSummary_longSuffix
              (α := α) hycut
      have hpEq :
          x.take k = y.take k :=
        Option.some.inj hpEqSome
      have hqEq :
          x.drop (x.length - l) =
            y.drop (y.length - l) :=
        Option.some.inj hqEqSome
      obtain ⟨mx, hmx⟩ :=
        exists_fixedWindow_middle x k l hfitx
      obtain ⟨my, hmy⟩ :=
        exists_fixedWindow_middle y k l hfity
      refine Or.inr
        ⟨hxcut, hycut,
          x.take k,
          x.drop (x.length - l),
          mx, my,
          fixedWindow_prefix_length x k l hfitx,
          fixedWindow_suffix_length x k l hfitx,
          ?_, ?_⟩
      · exact hmx
      · calc
          y =
              y.take k ++ my ++
                y.drop (y.length - l) := hmy
          _ =
              x.take k ++ my ++
                x.drop (x.length - l) := by
            rw [← hpEq, ← hqEq]

/-- The concrete summary equality relation is exactly the semantic one. -/
theorem fixedWindowRawSummary_eq_of_same
    {k l : Nat} {x y : Word α}
    (hsame : SameFixedWindowSummary k l x y) :
    fixedWindowRawSummary k l x =
      fixedWindowRawSummary k l y := by
  rcases hsame with hshort | hlong
  · rcases hshort with ⟨hx, rfl⟩
    rfl
  · rcases hlong with
      ⟨hxcut, hycut, p, q, mx, my,
        hp, hq, hx, hy⟩
    have hnotx :
        ¬ x.length < fixedWindowThreshold k l :=
      not_lt_of_ge hxcut
    have hnoty :
        ¬ y.length < fixedWindowThreshold k l :=
      not_lt_of_ge hycut
    have hsum :
        k + l ≤ fixedWindowThreshold k l := by
      unfold fixedWindowThreshold
      omega
    have hfitx : k + l ≤ x.length :=
      le_trans hsum hxcut
    have hfity : k + l ≤ y.length :=
      le_trans hsum hycut
    have hxp : x.take k = p := by
      rw [hx, List.append_assoc]
      exact take_append_of_prefix_length p (mx ++ q) k hp
    have hyp : y.take k = p := by
      rw [hy, List.append_assoc]
      exact take_append_of_prefix_length p (my ++ q) k hp
    have hxq :
        x.drop (x.length - l) = q := by
      rw [hx]
      have hindex :
          (p ++ mx ++ q).length - l =
            (p ++ mx).length := by
        simp only [List.length_append]
        omega
      rw [hindex]
      exact
        drop_append_of_prefix_length
          (p ++ mx) q (p ++ mx).length rfl
    have hyq :
        y.drop (y.length - l) = q := by
      rw [hy]
      have hindex :
          (p ++ my ++ q).length - l =
            (p ++ my).length := by
        simp only [List.length_append]
        omega
      rw [hindex]
      exact
        drop_append_of_prefix_length
          (p ++ my) q (p ++ my).length rfl
    unfold fixedWindowRawSummary
    rw [dif_neg hnotx, dif_neg hnoty]
    apply congrArg Sum.inr
    apply Prod.ext
    · apply Subtype.ext
      exact hxp.trans hyp.symm
    · apply Subtype.ext
      exact hxq.trans hyq.symm

theorem fixedWindowRawSummary_eq_iff
    {k l : Nat} {x y : Word α} :
    fixedWindowRawSummary k l x =
        fixedWindowRawSummary k l y
      ↔ SameFixedWindowSummary k l x y := by
  constructor
  · exact sameFixedWindowSummary_of_rawSummary_eq
  · exact fixedWindowRawSummary_eq_of_same

end FixedWindowConcreteSummary

end TCS1
end LeanCfgProject
