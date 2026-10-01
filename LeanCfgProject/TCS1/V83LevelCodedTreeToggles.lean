import LeanCfgProject.TCS1.V83LevelCodedTreeContexts

/-!
# TCS #1 v83: legal shortcut/clean toggles

The Appendix proof represents every parsed word by choosing shortcut nodes in
the clean height-n tree and moves between words by expanding or introducing
shortcuts.  This module formalizes that tree-level move system.

It proves that every level-n parsed tree is connected to the unique clean tree
by legal parsed-node toggles, hence any two parsed trees are connected by a
finite sequence of such toggles.  The remaining substitutability step is to
show that, when two serializations share a displayed prefix and suffix, the
needed toggles all lie inside the displayed factor.
-/

namespace LeanCfgProject
namespace TCS1

/-- One legal shortcut/clean replacement at a parsed residual-height node. -/
inductive LevelTreeToggle {n : Nat} :
    LevelTree n → LevelTree n → Prop
  | expand {i : Nat} (ctx : LevelTreeContext n i) :
      LevelTreeToggle
        (ctx.plug (.shortcut i))
        (ctx.plug (cleanLevelTree i))
  | contract {i : Nat} (ctx : LevelTreeContext n i) :
      LevelTreeToggle
        (ctx.plug (cleanLevelTree i))
        (ctx.plug (.shortcut i))

/-- One legal toggle is symmetric. -/
theorem levelTreeToggle_symm
    {n : Nat}
    {s t : LevelTree n}
    (h : LevelTreeToggle s t) :
    LevelTreeToggle t s := by
  cases h with
  | expand ctx =>
      exact LevelTreeToggle.contract ctx
  | contract ctx =>
      exact LevelTreeToggle.expand ctx

/--
At serialization level, every one-step toggle preserves a common external
prefix and suffix.
-/
theorem levelTreeToggle_serialized_context
    {n : Nat}
    {s t : LevelTree n}
    (h : LevelTreeToggle s t) :
    ∃ u v x y : Word LevelTreeSymbol,
      s.serialize = u ++ x ++ v ∧
      t.serialize = u ++ y ++ v := by
  cases h with
  | @expand i ctx =>
      obtain ⟨u, v, hs, ht⟩ :=
        levelTreeContext_shortcut_clean_same_context ctx
      exact
        ⟨u, v,
          (.shortcut i : LevelTree i).serialize,
          (cleanLevelTree i).serialize,
          hs, ht⟩
  | @contract i ctx =>
      obtain ⟨u, v, hs, ht⟩ :=
        levelTreeContext_shortcut_clean_same_context ctx
      exact
        ⟨u, v,
          (cleanLevelTree i).serialize,
          (.shortcut i : LevelTree i).serialize,
          ht, hs⟩

/-- Finite reflexive-transitive closure of parsed-node toggles. -/
inductive LevelTreeToggleReach {n : Nat} :
    LevelTree n → LevelTree n → Prop
  | refl (t : LevelTree n) :
      LevelTreeToggleReach t t
  | step {s t u : LevelTree n} :
      LevelTreeToggle s t →
      LevelTreeToggleReach t u →
      LevelTreeToggleReach s u

/-- Concatenate two finite toggle sequences. -/
theorem levelTreeToggleReach_trans
    {n : Nat}
    {s t u : LevelTree n}
    (hst : LevelTreeToggleReach s t)
    (htu : LevelTreeToggleReach t u) :
    LevelTreeToggleReach s u := by
  induction hst with
  | refl =>
      exact htu
  | @step a b t hab hbt ih =>
      exact LevelTreeToggleReach.step hab (ih htu)

/-- Reverse a finite toggle sequence. -/
theorem levelTreeToggleReach_symm
    {n : Nat}
    {s t : LevelTree n}
    (hst : LevelTreeToggleReach s t) :
    LevelTreeToggleReach t s := by
  induction hst with
  | refl t =>
      exact LevelTreeToggleReach.refl t
  | @step a b t hab hbt ih =>
      exact
        levelTreeToggleReach_trans
          ih
          (LevelTreeToggleReach.step
            (levelTreeToggle_symm hab)
            (LevelTreeToggleReach.refl a))

/-- Lift one toggle through a binary parent on the left child. -/
theorem levelTreeToggle_left
    {n : Nat}
    {s t : LevelTree n}
    (right : LevelTree n)
    (hst : LevelTreeToggle s t) :
    LevelTreeToggle
      (.node s right)
      (.node t right) := by
  cases hst with
  | @expand i ctx =>
      simpa [LevelTreeContext.plug] using
        (LevelTreeToggle.expand
          (LevelTreeContext.left ctx right))
  | @contract i ctx =>
      simpa [LevelTreeContext.plug] using
        (LevelTreeToggle.contract
          (LevelTreeContext.left ctx right))

/-- Lift one toggle through a binary parent on the right child. -/
theorem levelTreeToggle_right
    {n : Nat}
    (left : LevelTree n)
    {s t : LevelTree n}
    (hst : LevelTreeToggle s t) :
    LevelTreeToggle
      (.node left s)
      (.node left t) := by
  cases hst with
  | @expand i ctx =>
      simpa [LevelTreeContext.plug] using
        (LevelTreeToggle.expand
          (LevelTreeContext.right left ctx))
  | @contract i ctx =>
      simpa [LevelTreeContext.plug] using
        (LevelTreeToggle.contract
          (LevelTreeContext.right left ctx))

/-- Lift a finite toggle sequence through the left child of one binary node. -/
theorem levelTreeToggleReach_left
    {n : Nat}
    {s t : LevelTree n}
    (right : LevelTree n)
    (hst : LevelTreeToggleReach s t) :
    LevelTreeToggleReach
      (.node s right)
      (.node t right) := by
  induction hst with
  | refl s =>
      exact LevelTreeToggleReach.refl _
  | @step a b t hab hbt ih =>
      exact
        LevelTreeToggleReach.step
          (levelTreeToggle_left right hab)
          ih

/-- Lift a finite toggle sequence through the right child of one binary node. -/
theorem levelTreeToggleReach_right
    {n : Nat}
    (left : LevelTree n)
    {s t : LevelTree n}
    (hst : LevelTreeToggleReach s t) :
    LevelTreeToggleReach
      (.node left s)
      (.node left t) := by
  induction hst with
  | refl s =>
      exact LevelTreeToggleReach.refl _
  | @step a b t hab hbt ih =>
      exact
        LevelTreeToggleReach.step
          (levelTreeToggle_right left hab)
          ih

/-- Every parsed level-n tree can be expanded to the unique clean tree. -/
theorem levelTreeToggleReach_clean
    {n : Nat}
    (t : LevelTree n) :
    LevelTreeToggleReach t (cleanLevelTree n) := by
  induction t with
  | cleanLeaf =>
      exact LevelTreeToggleReach.refl _
  | shortcut n =>
      exact
        LevelTreeToggleReach.step
          (LevelTreeToggle.expand (LevelTreeContext.hole n))
          (LevelTreeToggleReach.refl _)
  | @node n left right ihL ihR =>
      have hL :
          LevelTreeToggleReach
            (.node left right)
            (.node (cleanLevelTree n) right) :=
        levelTreeToggleReach_left right ihL
      have hR :
          LevelTreeToggleReach
            (.node (cleanLevelTree n) right)
            (.node (cleanLevelTree n) (cleanLevelTree n)) :=
        levelTreeToggleReach_right (cleanLevelTree n) ihR
      simpa [cleanLevelTree] using
        levelTreeToggleReach_trans hL hR

/-- Any two parsed residual-height-n trees are connected by legal toggles. -/
theorem levelTreeToggleReach_connected
    {n : Nat}
    (s t : LevelTree n) :
    LevelTreeToggleReach s t := by
  exact
    levelTreeToggleReach_trans
      (levelTreeToggleReach_clean s)
      (levelTreeToggleReach_symm
        (levelTreeToggleReach_clean t))

end TCS1
end LeanCfgProject
