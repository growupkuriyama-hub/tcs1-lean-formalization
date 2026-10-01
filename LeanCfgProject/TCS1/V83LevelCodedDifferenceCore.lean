import LeanCfgProject.TCS1.V83LevelCodedNodeBodies
import LeanCfgProject.TCS1.V83LevelCodedTreeParsing

/-!
# TCS #1 v83: canonical difference cores for level-coded trees

For two distinct residual-height-n trees, the Appendix argument needs a
contiguous serialized interval containing every structural difference, with
equal material outside that interval.  This module constructs such a core
recursively.

The core factors are connected by literal body toggles.  Their first symbols
differ, and their last symbols differ (expressed as different heads after
reversal).  These endpoint facts are the key to showing that any common
displayed prefix/suffix must lie outside the core.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Every level-tree serialization ends with the right bracket. -/
theorem levelTree_serialize_ends_r
    {n : Nat}
    (t : LevelTree n) :
    ∃ pre : Word LevelTreeSymbol,
      t.serialize = pre ++ [r] := by
  cases t with
  | cleanLeaf =>
      exact ⟨[l, a], rfl⟩
  | shortcut n =>
      exact ⟨[l] ++ levelShortcutBody n, by
        simp [LevelTree.serialize, List.append_assoc]⟩
  | @node n left right =>
      exact
        ⟨[l] ++ left.serialize ++ right.serialize, by
          simp [LevelTree.serialize, List.append_assoc]⟩

/-- One root shortcut expansion, stated on node bodies. -/
theorem levelShortcutBody_reach_cleanBody
    (n : Nat) :
    LevelBodyToggleReach
      (levelShortcutBody n)
      (levelCleanNodeBody n) := by
  exact
    LevelBodyToggleReach.step
      (LevelBodyToggleStep.expand n [] [])
      (LevelBodyToggleReach.refl _)

/--
At positive residual height, the shortcut body can be expanded and then its
two clean children can be independently changed into arbitrary children.
-/
theorem levelShortcutBody_reach_nodeBody
    {n : Nat}
    (left right : LevelTree n) :
    LevelBodyToggleReach
      (levelShortcutBody (n + 1))
      (left.serialize ++ right.serialize) := by
  have hroot :
      LevelBodyToggleReach
        (levelShortcutBody (n + 1))
        (cleanLevelTreeWord n ++
          cleanLevelTreeWord n) := by
    simpa [levelCleanNodeBody] using
      levelShortcutBody_reach_cleanBody (n + 1)
  have hleft :
      LevelBodyToggleReach
        (cleanLevelTreeWord n)
        left.serialize :=
    levelTreeLanguage_bodyToggle_connected
      (cleanLevelTreeWord_mem_language n)
      ⟨left, rfl⟩
  have hright :
      LevelBodyToggleReach
        (cleanLevelTreeWord n)
        right.serialize :=
    levelTreeLanguage_bodyToggle_connected
      (cleanLevelTreeWord_mem_language n)
      ⟨right, rfl⟩
  have hleft' :
      LevelBodyToggleReach
        (cleanLevelTreeWord n ++
          cleanLevelTreeWord n)
        (left.serialize ++
          cleanLevelTreeWord n) := by
    simpa using
      levelBodyToggleReach_contextual
        hleft [] (cleanLevelTreeWord n)
  have hright' :
      LevelBodyToggleReach
        (left.serialize ++
          cleanLevelTreeWord n)
        (left.serialize ++ right.serialize) := by
    simpa using
      levelBodyToggleReach_contextual
        hright left.serialize []
  exact
    levelBodyToggleReach_trans hroot
      (levelBodyToggleReach_trans hleft' hright')

/-- The clean node body is never empty. -/
theorem levelCleanNodeBody_ne_nil
    (n : Nat) :
    levelCleanNodeBody n ≠ [] := by
  cases n with
  | zero =>
      simp [levelCleanNodeBody]
  | succ n =>
      obtain ⟨rest, hrest⟩ :=
        cleanLevelTreeWord_starts_l n
      simp [levelCleanNodeBody, hrest]

/-- A literal body-toggle step has a nonempty source and target. -/
theorem levelBodyToggleStep_nonempty
    {x y : Word LevelTreeSymbol}
    (h : LevelBodyToggleStep x y) :
    x ≠ [] ∧ y ≠ [] := by
  cases h with
  | expand i p q =>
      constructor
      · intro hx
        have hlen := congrArg List.length hx
        simp [levelShortcutBody_length] at hlen
      · intro hy
        have hlen := congrArg List.length hy
        have hb :
            0 < (levelCleanNodeBody i).length := by
          exact List.length_pos.mpr
            (levelCleanNodeBody_ne_nil i)
        simp only [List.length_append] at hlen
        omega
  | contract i p q =>
      constructor
      · intro hx
        have hlen := congrArg List.length hx
        have hb :
            0 < (levelCleanNodeBody i).length := by
          exact List.length_pos.mpr
            (levelCleanNodeBody_ne_nil i)
        simp only [List.length_append] at hlen
        omega
      · intro hy
        have hlen := congrArg List.length hy
        simp [levelShortcutBody_length] at hlen

/--
If a finite body-toggle reach has different first symbols, both endpoint
factors are nonempty.
-/
theorem levelBodyToggleReach_nonempty_of_head_ne
    {x y : Word LevelTreeSymbol}
    (hreach : LevelBodyToggleReach x y)
    (hhead : x.head? ≠ y.head?) :
    x ≠ [] ∧ y ≠ [] := by
  have hx : x ≠ [] := by
    intro hx0
    subst x
    cases hreach with
    | refl =>
        exact hhead rfl
    | @step _ b z hstep hrest =>
        exact (levelBodyToggleStep_nonempty hstep).1 rfl
  have hy : y ≠ [] := by
    have hsymm :=
      levelBodyToggleReach_symm hreach
    intro hy0
    subst y
    cases hsymm with
    | refl =>
        exact hhead rfl
    | @step _ b z hstep hrest =>
        exact (levelBodyToggleStep_nonempty hstep).1 rfl
  exact ⟨hx, hy⟩

/--
Canonical serialized difference core.

For equal trees we return the equality.  For distinct trees we return a
common outer prefix/suffix and middle factors connected by body toggles; the
middle factors differ at both their left and right endpoints.
-/
theorem levelTree_difference_core
    {n : Nat}
    (s t : LevelTree n) :
    s = t ∨
      ∃ p q x y : Word LevelTreeSymbol,
        s.serialize = p ++ x ++ q ∧
        t.serialize = p ++ y ++ q ∧
        LevelBodyToggleReach x y ∧
        x.head? ≠ y.head? ∧
        x.reverse.head? ≠ y.reverse.head? := by
  induction s generalizing t with
  | cleanLeaf =>
      cases t with
      | cleanLeaf =>
          exact Or.inl rfl
      | shortcut n =>
          right
          refine ⟨[l], [r], [a],
            levelShortcutBody 0, ?_, ?_, ?_, ?_, ?_⟩
          · rfl
          · simp [LevelTree.serialize, List.append_assoc]
          · exact
              levelBodyToggleReach_symm
                (levelShortcutBody_reach_cleanBody 0)
          · simp [levelShortcutBody]
          · simp [levelShortcutBody]
  | shortcut k =>
      cases t with
      | cleanLeaf =>
          right
          refine ⟨[l], [r],
            levelShortcutBody 0, [a],
            ?_, ?_, ?_, ?_, ?_⟩
          · simp [LevelTree.serialize, List.append_assoc]
          · rfl
          · exact levelShortcutBody_reach_cleanBody 0
          · simp [levelShortcutBody]
          · simp [levelShortcutBody]
      | shortcut k' =>
          have hk : k = k' := by omega
          subst k'
          exact Or.inl rfl
      | @node j left right =>
          right
          refine ⟨[l], [r],
            levelShortcutBody (j + 1),
            left.serialize ++ right.serialize,
            ?_, ?_, ?_, ?_, ?_⟩
          · simp [LevelTree.serialize, List.append_assoc]
          · simp [LevelTree.serialize, List.append_assoc]
          · exact
              levelShortcutBody_reach_nodeBody left right
          · obtain ⟨rest, hrest⟩ :=
              levelTree_serialize_starts_l left
            rw [hrest]
            simp [levelShortcutBody]
          · obtain ⟨pre, hpre⟩ :=
              levelTree_serialize_ends_r right
            rw [hpre]
            simp [levelShortcutBody, List.reverse_append]
  | @node j left right ihL ihR =>
      cases t with
      | shortcut k =>
          right
          refine ⟨[l], [r],
            left.serialize ++ right.serialize,
            levelShortcutBody (j + 1),
            ?_, ?_, ?_, ?_, ?_⟩
          · simp [LevelTree.serialize, List.append_assoc]
          · simp [LevelTree.serialize, List.append_assoc]
          · exact
              levelBodyToggleReach_symm
                (levelShortcutBody_reach_nodeBody left right)
          · obtain ⟨rest, hrest⟩ :=
              levelTree_serialize_starts_l left
            rw [hrest]
            simp [levelShortcutBody]
          · obtain ⟨pre, hpre⟩ :=
              levelTree_serialize_ends_r right
            rw [hpre]
            simp [levelShortcutBody, List.reverse_append]
      | @node _ left' right' =>
          rcases ihL left' with hLeq | hLdiff
          · subst left'
            rcases ihR right' with hReq | hRdiff
            · subst right'
              exact Or.inl rfl
            · right
              rcases hRdiff with
                ⟨pR, qR, xR, yR,
                  hsR, htR, hreachR,
                  hheadR, htailR⟩
              refine
                ⟨[l] ++ left.serialize ++ pR,
                  qR ++ [r], xR, yR,
                  ?_, ?_, hreachR,
                  hheadR, htailR⟩
              · rw [LevelTree.serialize, hsR]
                simp [List.append_assoc]
              · rw [LevelTree.serialize, htR]
                simp [List.append_assoc]
          · rcases ihR right' with hReq | hRdiff
            · subst right'
              right
              rcases hLdiff with
                ⟨pL, qL, xL, yL,
                  hsL, htL, hreachL,
                  hheadL, htailL⟩
              refine
                ⟨[l] ++ pL,
                  qL ++ right.serialize ++ [r],
                  xL, yL, ?_, ?_, hreachL,
                  hheadL, htailL⟩
              · rw [LevelTree.serialize, hsL]
                simp [List.append_assoc]
              · rw [LevelTree.serialize, htL]
                simp [List.append_assoc]
            · right
              rcases hLdiff with
                ⟨pL, qL, xL, yL,
                  hsL, htL, hreachL,
                  hheadL, htailL⟩
              rcases hRdiff with
                ⟨pR, qR, xR, yR,
                  hsR, htR, hreachR,
                  hheadR, htailR⟩
              let mid : Word LevelTreeSymbol :=
                qL ++ pR
              let coreS : Word LevelTreeSymbol :=
                xL ++ mid ++ xR
              let coreT : Word LevelTreeSymbol :=
                yL ++ mid ++ yR
              have hfirst :
                  LevelBodyToggleReach
                    coreS
                    (yL ++ mid ++ xR) := by
                dsimp [coreS, coreT, mid]
                simpa [List.append_assoc] using
                  levelBodyToggleReach_contextual
                    hreachL []
                    (qL ++ pR ++ xR)
              have hsecond :
                  LevelBodyToggleReach
                    (yL ++ mid ++ xR)
                    coreT := by
                dsimp [coreS, coreT, mid]
                simpa [List.append_assoc] using
                  levelBodyToggleReach_contextual
                    hreachR (yL ++ qL ++ pR) []
              have hreach :
                  LevelBodyToggleReach coreS coreT :=
                levelBodyToggleReach_trans
                  hfirst hsecond
              refine
                ⟨[l] ++ pL, qR ++ [r],
                  coreS, coreT,
                  ?_, ?_, hreach, ?_, ?_⟩
              · rw [LevelTree.serialize, hsL, hsR]
                simp [coreS, mid, List.append_assoc]
              · rw [LevelTree.serialize, htL, htR]
                simp [coreT, mid, List.append_assoc]
              · dsimp [coreS, coreT, mid]
                obtain ⟨hxL, hyL⟩ :=
                  levelBodyToggleReach_nonempty_of_head_ne
                    hreachL hheadL
                rw [List.head?_append_of_ne_nil xL hxL,
                    List.head?_append_of_ne_nil yL hyL]
                exact hheadL
              · dsimp [coreS, coreT, mid]
                simp only [List.reverse_append]
                obtain ⟨hxR, hyR⟩ :=
                  levelBodyToggleReach_nonempty_of_head_ne
                    hreachR hheadR
                have hxRev : xR.reverse ≠ [] := by
                  simpa using hxR
                have hyRev : yR.reverse ≠ [] := by
                  simpa using hyR
                rw [List.head?_append_of_ne_nil xR.reverse hxRev,
                    List.head?_append_of_ne_nil yR.reverse hyRev]
                exact htailR


/--
If two words have the same displayed prefix u, while a smaller common prefix p
is followed by nonempty factors with different first symbols, then u cannot
extend into those factors: u is a prefix of p.
-/
theorem commonPrefix_stops_before_distinct_heads
    {α : Type}
    {p q u v x y X Y : List α}
    (hx : x ≠ [])
    (hy : y ≠ [])
    (hhead : x.head? ≠ y.head?)
    (hs : p ++ x ++ q = u ++ X ++ v)
    (ht : p ++ y ++ q = u ++ Y ++ v) :
    ∃ a : List α, p = u ++ a := by
  induction p generalizing u with
  | nil =>
      cases u with
      | nil =>
          exact ⟨[], rfl⟩
      | cons uh ut =>
          cases x with
          | nil =>
              exact False.elim (hx rfl)
          | cons xh xt =>
              cases y with
              | nil =>
                  exact False.elim (hy rfl)
              | cons yh yt =>
                  simp only [List.nil_append, List.cons_append] at hs ht
                  have hxuh : xh = uh := by
                    exact congrArg List.head hs
                  have hyuh : yh = uh := by
                    exact congrArg List.head ht
                  exfalso
                  apply hhead
                  simp [hxuh, hyuh]
  | cons ph pt ih =>
      cases u with
      | nil =>
          exact ⟨ph :: pt, rfl⟩
      | cons uh ut =>
          simp only [List.cons_append] at hs ht
          have hph : ph = uh := by
            exact congrArg List.head hs
          have hsTail :
              pt ++ x ++ q = ut ++ X ++ v := by
            simpa [hph] using congrArg List.tail hs
          have htTail :
              pt ++ y ++ q = ut ++ Y ++ v := by
            simpa [hph] using congrArg List.tail ht
          obtain ⟨a, ha⟩ :=
            ih (u := ut) hx hy hhead hsTail htTail
          refine ⟨a, ?_⟩
          simp [hph, ha]

/--
Dual suffix form of the preceding lemma, obtained by reversing the two
factorizations.
-/
theorem commonSuffix_stops_after_distinct_tails
    {α : Type}
    {p q u v x y X Y : List α}
    (hx : x ≠ [])
    (hy : y ≠ [])
    (htail : x.reverse.head? ≠ y.reverse.head?)
    (hs : p ++ x ++ q = u ++ X ++ v)
    (ht : p ++ y ++ q = u ++ Y ++ v) :
    ∃ b : List α, q = b ++ v := by
  have hsR :
      q.reverse ++ x.reverse ++ p.reverse =
        v.reverse ++ X.reverse ++ u.reverse := by
    simpa [List.reverse_append, List.append_assoc] using
      congrArg List.reverse hs
  have htR :
      q.reverse ++ y.reverse ++ p.reverse =
        v.reverse ++ Y.reverse ++ u.reverse := by
    simpa [List.reverse_append, List.append_assoc] using
      congrArg List.reverse ht
  have hxR : x.reverse ≠ [] := by
    simpa using hx
  have hyR : y.reverse ≠ [] := by
    simpa using hy
  obtain ⟨a, ha⟩ :=
    commonPrefix_stops_before_distinct_heads
      hxR hyR htail hsR htR
  refine ⟨a.reverse, ?_⟩
  have hrev := congrArg List.reverse ha
  simpa [List.reverse_append] using hrev

/--
A difference core whose endpoints disagree must lie inside every other common
prefix/suffix factorization of the same two words.
-/
theorem differenceCore_nested_in_common_factor
    {α : Type}
    {A B p q u v x y X Y : List α}
    (hx : x ≠ [])
    (hy : y ≠ [])
    (hhead : x.head? ≠ y.head?)
    (htail : x.reverse.head? ≠ y.reverse.head?)
    (hAcore : A = p ++ x ++ q)
    (hBcore : B = p ++ y ++ q)
    (hAouter : A = u ++ X ++ v)
    (hBouter : B = u ++ Y ++ v) :
    ∃ a b : List α,
      X = a ++ x ++ b ∧
      Y = a ++ y ++ b := by
  have hs :
      p ++ x ++ q = u ++ X ++ v :=
    hAcore.symm.trans hAouter
  have ht :
      p ++ y ++ q = u ++ Y ++ v :=
    hBcore.symm.trans hBouter
  obtain ⟨a, hp⟩ :=
    commonPrefix_stops_before_distinct_heads
      hx hy hhead hs ht
  obtain ⟨b, hq⟩ :=
    commonSuffix_stops_after_distinct_tails
      hx hy htail hs ht
  have hs' :
      u ++ (a ++ x ++ b) ++ v =
        u ++ X ++ v := by
    simpa [hp, hq, List.append_assoc] using hs
  have ht' :
      u ++ (a ++ y ++ b) ++ v =
        u ++ Y ++ v := by
    simpa [hp, hq, List.append_assoc] using ht
  have hsLeft :
      (a ++ x ++ b) ++ v = X ++ v := by
    exact
      List.append_right_injective u
        (by simpa [List.append_assoc] using hs')
  have htLeft :
      (a ++ y ++ b) ++ v = Y ++ v := by
    exact
      List.append_right_injective u
        (by simpa [List.append_assoc] using ht')
  have hxEq :
      a ++ x ++ b = X :=
    List.append_left_injective v hsLeft
  have hyEq :
      a ++ y ++ b = Y :=
    List.append_left_injective v htLeft
  exact ⟨a, b, hxEq.symm, hyEq.symm⟩

end TCS1
end LeanCfgProject
