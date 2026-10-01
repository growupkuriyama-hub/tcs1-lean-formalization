import LeanCfgProject.TCS1.V83LevelCodedOccurrenceKernel
import LeanCfgProject.TCS1.V83LevelCodedNodeBodies

/-!
# TCS #1 v83: recognition of clean subtree and clean-node-body occurrences

This module complements shortcut-body recognition.  It gives a structural
decomposition of a tree zipper at the immediate parent of its hole, then uses
the verified prefix parser to show that literal clean serializations and clean
node bodies can only occur at genuine parsed nodes of the matching residual
height.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/--
Decompose a level-tree context at the immediate parent of its hole.

The first alternative is the root hole.  In the second, the hole subtree is
the left child of its immediate parent; in the third it is the right child.
Only the serialized prefix/suffix equations are needed downstream.
-/
theorem levelTreeContext_immediate_frame
    {n i : Nat}
    (ctx : LevelTreeContext n i) :
    (n = i ∧ ctx.prefix = [] ∧ ctx.suffix = []) ∨
    (∃ outer : LevelTreeContext n (i + 1),
       ∃ sibling : LevelTree i,
         ctx.prefix = outer.prefix ++ [l] ∧
         ctx.suffix =
           sibling.serialize ++ [r] ++ outer.suffix) ∨
    (∃ outer : LevelTreeContext n (i + 1),
       ∃ sibling : LevelTree i,
         ctx.prefix =
           outer.prefix ++ [l] ++ sibling.serialize ∧
         ctx.suffix = [r] ++ outer.suffix) := by
  induction ctx with
  | hole i =>
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | @left j i inner sibling ih =>
      rcases ih with hroot | hframe
      · rcases hroot with ⟨hji, hp, hq⟩
        subst j
        right
        left
        refine
          ⟨LevelTreeContext.hole (i + 1),
            sibling, ?_, ?_⟩
        · simp [LevelTreeContext.prefix, hp]
        · simp [LevelTreeContext.suffix, hq,
            List.append_assoc]
      · rcases hframe with hleft | hright
        · rcases hleft with
            ⟨outer, sib, hp, hq⟩
          right
          left
          refine
            ⟨LevelTreeContext.left outer sibling,
              sib, ?_, ?_⟩
          · simp [LevelTreeContext.prefix, hp,
              List.append_assoc]
          · simp [LevelTreeContext.suffix, hq,
              List.append_assoc]
        · rcases hright with
            ⟨outer, sib, hp, hq⟩
          right
          right
          refine
            ⟨LevelTreeContext.left outer sibling,
              sib, ?_, ?_⟩
          · simp [LevelTreeContext.prefix, hp,
              List.append_assoc]
          · simp [LevelTreeContext.suffix, hq,
              List.append_assoc]
  | @right j i sibling inner ih =>
      rcases ih with hroot | hframe
      · rcases hroot with ⟨hji, hp, hq⟩
        subst j
        right
        right
        refine
          ⟨LevelTreeContext.hole (i + 1),
            sibling, ?_, ?_⟩
        · simp [LevelTreeContext.prefix, hp,
            List.append_assoc]
        · simp [LevelTreeContext.suffix, hq]
      · rcases hframe with hleft | hright
        · rcases hleft with
            ⟨outer, sib, hp, hq⟩
          right
          left
          refine
            ⟨LevelTreeContext.right sibling outer,
              sib, ?_, ?_⟩
          · simp [LevelTreeContext.prefix, hp,
              List.append_assoc]
          · simp [LevelTreeContext.suffix, hq,
              List.append_assoc]
        · rcases hright with
            ⟨outer, sib, hp, hq⟩
          right
          right
          refine
            ⟨LevelTreeContext.right sibling outer,
              sib, ?_, ?_⟩
          · simp [LevelTreeContext.prefix, hp,
              List.append_assoc]
          · simp [LevelTreeContext.suffix, hq,
              List.append_assoc]

/-- No designated a can occur in a shortcut serialization. -/
theorem no_a_factor_in_shortcut
    (i : Nat)
    {p q : Word LevelTreeSymbol} :
    ¬ ((LevelTree.shortcut i).serialize =
        p ++ a :: q) := by
  intro h
  have ha :
      a ∈ (LevelTree.shortcut i).serialize := by
    rw [h]
    simp
  simpa [LevelTree.serialize, levelShortcutBody] using ha

/--
A designated a in a valid serialization is exactly the body of a parsed clean
leaf, with the exact surrounding prefix and suffix.
-/
theorem levelTree_a_factor_context
    {n : Nat}
    (t : LevelTree n)
    {p q : Word LevelTreeSymbol}
    (h : t.serialize = p ++ a :: q) :
    ∃ ctx : LevelTreeContext n 0,
      p = ctx.prefix ++ [l] ∧
      q = [r] ++ ctx.suffix := by
  induction t generalizing p q with
  | cleanLeaf =>
      have hcanon :
          ([l] : Word LevelTreeSymbol) ++
              a :: ([r] : Word LevelTreeSymbol) =
            p ++ a :: q := by
        simpa [LevelTree.serialize] using h
      have hinj :=
        (List.append_cons_inj_of_notMem
          (x₁ := ([l] : Word LevelTreeSymbol))
          (x₂ := p)
          (z₁ := ([r] : Word LevelTreeSymbol))
          (z₂ := q)
          (a₁ := a) (a₂ := a)
          (by simp)
          (by simp)).1 hcanon
      rcases hinj with ⟨hp, _, hq⟩
      refine
        ⟨LevelTreeContext.hole 0, ?_, ?_⟩
      · simpa [LevelTreeContext.prefix] using hp.symm
      · simpa [LevelTreeContext.suffix] using hq.symm
  | shortcut i =>
      exact False.elim (no_a_factor_in_shortcut i h)
  | @node j left right ihL ihR =>
      have houter :
          ([l] : Word LevelTreeSymbol) ++
              (left.serialize ++ right.serialize ++ [r]) =
            p ++ a :: q := by
        simpa [LevelTree.serialize,
          List.append_assoc] using h
      rcases
          factor_cons_split_append
            a ([l] : Word LevelTreeSymbol)
            (left.serialize ++ right.serialize ++ [r])
            p q houter with
        hInL | hAfterL
      · rcases hInL with
          ⟨p0, q0, hbad, _, _⟩
        have ha : a ∈ ([l] : Word LevelTreeSymbol) := by
          rw [hbad]
          simp
        simp at ha
      · rcases hAfterL with
          ⟨p1, q1, hrest, hp, hq⟩
        rcases
            factor_cons_split_append
              a left.serialize
              (right.serialize ++ [r])
              p1 q1 hrest with
          hInLeft | hAfterLeft
        · rcases hInLeft with
            ⟨pL, qL, hLeft, hp1, hq1⟩
          obtain ⟨ctx, hpL, hqLctx⟩ :=
            ihL hLeft
          refine
            ⟨LevelTreeContext.left ctx right,
              ?_, ?_⟩
          · rw [hp, hp1, hpL]
            simp [LevelTreeContext.prefix,
              List.append_assoc]
          · rw [hq, hq1, hqLctx]
            simp [LevelTreeContext.suffix,
              List.append_assoc]
        · rcases hAfterLeft with
            ⟨p2, q2, hRightTail, hp1, hq1⟩
          rcases
              factor_cons_split_append
                a right.serialize ([r] : Word LevelTreeSymbol)
                p2 q2 hRightTail with
            hInRight | hInFinalR
          · rcases hInRight with
              ⟨pR, qR, hRight, hp2, hq2⟩
            obtain ⟨ctx, hpR, hqRctx⟩ :=
              ihR hRight
            refine
              ⟨LevelTreeContext.right left ctx,
                ?_, ?_⟩
            · rw [hp, hp1, hp2, hpR]
              simp [LevelTreeContext.prefix,
                List.append_assoc]
            · rw [hq, hq1, hq2, hqRctx]
              simp [LevelTreeContext.suffix,
                List.append_assoc]
          · rcases hInFinalR with
              ⟨pR, qR, hbad, _, _⟩
            have ha : a ∈ ([r] : Word LevelTreeSymbol) := by
              rw [hbad]
              simp
            simp at ha

/--
A literal clean serialization z_i occurring in a valid level-n serialization
is exactly a parsed residual-height-i subtree.
-/
theorem cleanLevelTreeWord_factor_context
    (n i : Nat)
    {p q : Word LevelTreeSymbol}
    (hmem :
      p ++ cleanLevelTreeWord i ++ q ∈
        LevelTreeLanguage n) :
    ∃ ctx : LevelTreeContext n i,
      p = ctx.prefix ∧ q = ctx.suffix := by
  induction i generalizing p q with
  | zero =>
      rcases hmem with ⟨t, ht⟩
      have haFactor :
          t.serialize =
            (p ++ [l]) ++ a ::
              ([r] ++ q) := by
        rw [ht]
        simp [cleanLevelTreeWord, cleanLevelTree,
          LevelTree.serialize, List.append_assoc]
      obtain ⟨ctx, hp, hq⟩ :=
        levelTree_a_factor_context t haFactor
      refine ⟨ctx, ?_, ?_⟩
      · have hpc :
            p ++ [l] =
              ctx.prefix ++ [l] := hp
        exact List.append_left_injective [l] hpc
      · have hqc :
            [r] ++ q =
              [r] ++ ctx.suffix := hq
        exact List.append_right_injective [r] hqc
  | succ i ih =>
      rcases hmem with ⟨t, ht⟩
      have hfirst :
          (p ++ [l]) ++ cleanLevelTreeWord i ++
              (cleanLevelTreeWord i ++ [r] ++ q) ∈
            LevelTreeLanguage n := by
        refine ⟨t, ?_⟩
        rw [ht]
        simp [cleanLevelTreeWord, cleanLevelTree,
          LevelTree.serialize, List.append_assoc]
      obtain ⟨ctx, hp, hq⟩ :=
        ih hfirst
      rcases levelTreeContext_immediate_frame ctx with
        hroot | hframe
      · rcases hroot with ⟨_, _, hsuf⟩
        rw [hsuf] at hq
        have hnonempty :
            cleanLevelTreeWord i ++ [r] ++ q ≠ [] := by
          obtain ⟨rest, hstart⟩ :=
            cleanLevelTreeWord_starts_l i
          rw [hstart]
          simp
        exact False.elim (hnonempty hq)
      · rcases hframe with hleft | hright
        · rcases hleft with
            ⟨outer, sibling, hpre, hsuf⟩
          have heq :
              cleanLevelTreeWord i ++ [r] ++ q =
                sibling.serialize ++ [r] ++
                  outer.suffix := by
            exact hq.trans hsuf
          have hparse :=
            congrArg (parseLevelTreePrefix i) heq
          simp at hparse
          have hsib :
              sibling = cleanLevelTree i := by
            exact congrArg Prod.fst
              (Option.some.inj hparse)
          have htail :
              [r] ++ q =
                [r] ++ outer.suffix := by
            exact congrArg Prod.snd
              (Option.some.inj hparse)
          refine ⟨outer, ?_, ?_⟩
          · have hp' :
                p ++ [l] =
                  outer.prefix ++ [l] := by
              exact hp.trans hpre
            exact List.append_left_injective [l] hp'
          · exact
              List.append_right_injective [r] htail
        · rcases hright with
            ⟨outer, sibling, hpre, hsuf⟩
          have heq :
              cleanLevelTreeWord i ++ [r] ++ q =
                [r] ++ outer.suffix := by
            exact hq.trans hsuf
          obtain ⟨rest, hstart⟩ :=
            cleanLevelTreeWord_starts_l i
          rw [hstart] at heq
          simp at heq

/--
The literal clean node body b_i can only occur as the body of a genuine parsed
residual-height-i clean node.
-/
theorem levelCleanBodyRecognition_proved
    (n : Nat) :
    ∀ {i : Nat}
      {p q : Word LevelTreeSymbol},
      p ++ levelCleanNodeBody i ++ q ∈
          LevelTreeLanguage n →
      ∃ ctx : LevelTreeContext n i,
        p = ctx.prefix ++ [l] ∧
        q = [r] ++ ctx.suffix := by
  intro i p q hmem
  cases i with
  | zero =>
      rcases hmem with ⟨t, ht⟩
      have haFactor :
          t.serialize = p ++ a :: q := by
        rw [ht]
        simpa [levelCleanNodeBody] using rfl
      exact levelTree_a_factor_context t haFactor
  | succ i =>
      have hfirst :
          p ++ cleanLevelTreeWord i ++
              (cleanLevelTreeWord i ++ q) ∈
            LevelTreeLanguage n := by
        simpa [levelCleanNodeBody,
          List.append_assoc] using hmem
      obtain ⟨ctx, hp, hq⟩ :=
        cleanLevelTreeWord_factor_context
          n i hfirst
      rcases levelTreeContext_immediate_frame ctx with
        hroot | hframe
      · rcases hroot with ⟨_, _, hsuf⟩
        rw [hsuf] at hq
        obtain ⟨rest, hstart⟩ :=
          cleanLevelTreeWord_starts_l i
        rw [hstart] at hq
        simp at hq
      · rcases hframe with hleft | hright
        · rcases hleft with
            ⟨outer, sibling, hpre, hsuf⟩
          have heq :
              cleanLevelTreeWord i ++ q =
                sibling.serialize ++ [r] ++
                  outer.suffix := by
            exact hq.trans hsuf
          have hparse :=
            congrArg (parseLevelTreePrefix i) heq
          simp at hparse
          have htail :
              q = [r] ++ outer.suffix := by
            exact congrArg Prod.snd
              (Option.some.inj hparse)
          refine ⟨outer, ?_, htail⟩
          exact hp.trans hpre
        · rcases hright with
            ⟨outer, sibling, hpre, hsuf⟩
          have heq :
              cleanLevelTreeWord i ++ q =
                [r] ++ outer.suffix := by
            exact hq.trans hsuf
          obtain ⟨rest, hstart⟩ :=
            cleanLevelTreeWord_starts_l i
          rw [hstart] at heq
          simp at heq

end TCS1
end LeanCfgProject
