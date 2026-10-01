import LeanCfgProject.TCS1.V83LevelCodedNodeBodies
import LeanCfgProject.TCS1.V83LevelCodedDifferenceCore
import LeanCfgProject.TCS1.ClarkEyraudSpecialCase

/-!
# TCS #1 v83: substitutability bridge for the level-coded Appendix proof

The Appendix proof has two genuinely combinatorial ingredients:

1. literal node-body replacements s_i <-> b_i are admissible in every valid
   level-n serialization; and
2. if u x v and u y v are both valid level-n serializations, the differences
   between the two parses can be realized by a finite body-toggle sequence
   entirely inside x/y.

This file isolates those obligations and proves that together they imply the
paper-facing Clark--Eyraud substitutability statement.  Thus the remaining
formal work is concentrated exactly where the prose proof uses unique parsing
and cut-locality.
-/

namespace LeanCfgProject
namespace TCS1

/--
Every legal literal body step can be replayed inside an arbitrary surrounding
word context without leaving T_n.
-/
def LevelBodyToggleAdmissible (n : Nat) : Prop :=
  ∀ {x y : Word LevelTreeSymbol},
    LevelBodyToggleStep x y →
    ∀ (u v : Word LevelTreeSymbol),
      u ++ x ++ v ∈ LevelTreeLanguage n →
      u ++ y ++ v ∈ LevelTreeLanguage n

/--
Recognition statement for a literal shortcut body occurrence in a valid
level-n serialization: the occurrence is exactly the body of a parsed
residual-height-i node.
-/
def LevelShortcutBodyRecognition (n : Nat) : Prop :=
  ∀ {i : Nat}
    {p q : Word LevelTreeSymbol},
    p ++ levelShortcutBody i ++ q ∈
        LevelTreeLanguage n →
    ∃ ctx : LevelTreeContext n i,
      p = ctx.prefix ++ [LevelTreeSymbol.l] ∧
      q = [LevelTreeSymbol.r] ++ ctx.suffix

/--
Recognition statement for a clean body occurrence: it is exactly the body of
a parsed residual-height-i clean node.
-/
def LevelCleanBodyRecognition (n : Nat) : Prop :=
  ∀ {i : Nat}
    {p q : Word LevelTreeSymbol},
    p ++ levelCleanNodeBody i ++ q ∈
        LevelTreeLanguage n →
    ∃ ctx : LevelTreeContext n i,
      p = ctx.prefix ++ [LevelTreeSymbol.l] ∧
      q = [LevelTreeSymbol.r] ++ ctx.suffix

/--
The two literal-occurrence recognition lemmas imply replay admissibility of
every body toggle.
-/
theorem levelBodyToggleAdmissible_of_recognition
    (n : Nat)
    (hshort : LevelShortcutBodyRecognition n)
    (hclean : LevelCleanBodyRecognition n) :
    LevelBodyToggleAdmissible n := by
  intro x y hstep u v hmem
  cases hstep with
  | expand i p q =>
      have hwhole :
          (u ++ p) ++ levelShortcutBody i ++
              (q ++ v) ∈ LevelTreeLanguage n := by
        simpa [List.append_assoc] using hmem
      obtain ⟨ctx, hp, hq⟩ :=
        hshort hwhole
      have hcleanMem :=
        levelTreeContext_clean_mem ctx
      rw [levelTreeContext_clean_body_factor] at hcleanMem
      have hrepl :
          (u ++ p) ++ levelCleanNodeBody i ++
              (q ++ v) ∈ LevelTreeLanguage n := by
        rw [hp, hq]
        exact hcleanMem
      simpa [List.append_assoc] using hrepl
  | contract i p q =>
      have hwhole :
          (u ++ p) ++ levelCleanNodeBody i ++
              (q ++ v) ∈ LevelTreeLanguage n := by
        simpa [List.append_assoc] using hmem
      obtain ⟨ctx, hp, hq⟩ :=
        hclean hwhole
      have hshortMem :=
        levelTreeContext_shortcut_mem ctx
      rw [levelTreeContext_shortcut_body_factor] at hshortMem
      have hrepl :
          (u ++ p) ++ levelShortcutBody i ++
              (q ++ v) ∈ LevelTreeLanguage n := by
        rw [hp, hq]
        exact hshortMem
      simpa [List.append_assoc] using hrepl

/--
Common displayed prefix/suffix force the required tree differences to be
realizable entirely inside the displayed factor.
-/
def LevelBodyToggleCutLocality (n : Nat) : Prop :=
  ∀ {u v x y : Word LevelTreeSymbol},
    u ++ x ++ v ∈ LevelTreeLanguage n →
    u ++ y ++ v ∈ LevelTreeLanguage n →
    LevelBodyToggleReach x y

/--
The Appendix cut-locality statement is a theorem: every canonical structural
difference core lies inside the displayed factor between a common prefix and
suffix.
-/
theorem levelBodyToggleCutLocality_levelTree
    (n : Nat) :
    LevelBodyToggleCutLocality n := by
  intro u v x y hux huy
  rcases hux with ⟨s, hs⟩
  rcases huy with ⟨t, ht⟩
  rcases levelTree_difference_core s t with hEq | hDiff
  · subst t
    have hxy :
        u ++ x ++ v = u ++ y ++ v := by
      exact hs.symm.trans ht
    have hxyLeft :
        x ++ v = y ++ v :=
      List.append_right_injective u
        (by simpa [List.append_assoc] using hxy)
    have hxyCore : x = y :=
      List.append_left_injective v hxyLeft
    subst y
    exact LevelBodyToggleReach.refl x
  · rcases hDiff with
      ⟨p, q, coreX, coreY,
        hsCore, htCore, hreach,
        hhead, htail⟩
    obtain ⟨hxne, hyne⟩ :=
      levelBodyToggleReach_nonempty_of_head_ne
        hreach hhead
    obtain ⟨a, b, hx, hy⟩ :=
      differenceCore_nested_in_common_factor
        hxne hyne hhead htail
        hsCore htCore hs ht
    rw [hx, hy]
    exact
      levelBodyToggleReach_contextual
        hreach a b

/-- Admissibility transports language membership along a finite body sequence. -/
theorem levelBodyToggleReach_transport
    {n : Nat}
    (hadm : LevelBodyToggleAdmissible n)
    {x y : Word LevelTreeSymbol}
    (hxy : LevelBodyToggleReach x y)
    (u v : Word LevelTreeSymbol)
    (hx : u ++ x ++ v ∈ LevelTreeLanguage n) :
    u ++ y ++ v ∈ LevelTreeLanguage n := by
  induction hxy with
  | refl =>
      exact hx
  | @step a b y hab hby ih =>
      have hb :
          u ++ b ++ v ∈ LevelTreeLanguage n :=
        hadm hab u v hx
      exact ih hb

/--
The two Appendix combinatorial obligations imply Clark--Eyraud
substitutability of T_n.
-/
theorem levelTree_clarkEyraud_of_admissible_cutLocal
    (n : Nat)
    (hadm : LevelBodyToggleAdmissible n)
    (hlocal : LevelBodyToggleCutLocality n) :
    ClarkEyraudSubstitutableOn
      (LevelTreeLanguage n) := by
  intro x y _hxne _hyne hshared
  rcases hshared with ⟨u, v, hux, huy⟩
  have hxy : LevelBodyToggleReach x y :=
    hlocal hux huy
  have hyx : LevelBodyToggleReach y x :=
    levelBodyToggleReach_symm hxy
  apply Set.ext
  intro c
  constructor
  · intro hc
    have hxmem :
        c.1 ++ x ++ c.2 ∈ LevelTreeLanguage n := by
      simpa [Distribution] using hc
    have hymem :=
      levelBodyToggleReach_transport
        hadm hxy c.1 c.2 hxmem
    simpa [Distribution] using hymem
  · intro hc
    have hymem :
        c.1 ++ y ++ c.2 ∈ LevelTreeLanguage n := by
      simpa [Distribution] using hc
    have hxmem :=
      levelBodyToggleReach_transport
        hadm hyx c.1 c.2 hymem
    simpa [Distribution] using hxmem

end TCS1
end LeanCfgProject
