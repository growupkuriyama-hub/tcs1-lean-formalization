import LeanCfgProject.TCS1.V83LevelCodedTreeToggles

/-!
# TCS #1 v83: node bodies for the Appendix replacement argument

The manuscript's Appendix toggles the *body* of a parsed residual-height-i
node,

  s_i <-> b_i,

while keeping that node's surrounding l/r brackets fixed.  The tree zipper
developed earlier focused whole subtrees; this module refines the
serialization factorization to the exact body-level replacement used in the
paper.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Clean body b_0 = a and b_(i+1) = z_i z_i. -/
def levelCleanNodeBody : Nat → Word LevelTreeSymbol
  | 0 => [a]
  | i + 1 => cleanLevelTreeWord i ++ cleanLevelTreeWord i

/-- The clean residual-height-i tree is l b_i r. -/
theorem cleanLevelTree_serialize_eq_bracket_body
    (i : Nat) :
    (cleanLevelTree i).serialize =
      [l] ++ levelCleanNodeBody i ++ [r] := by
  cases i with
  | zero =>
      simp [cleanLevelTree, LevelTree.serialize,
        levelCleanNodeBody]
  | succ i =>
      simp [cleanLevelTree, LevelTree.serialize,
        levelCleanNodeBody, cleanLevelTreeWord,
        List.append_assoc]

/-- The shortcut residual-height-i tree is l s_i r. -/
theorem shortcutLevelTree_serialize_eq_bracket_body
    (i : Nat) :
    (LevelTree.shortcut i).serialize =
      [l] ++ levelShortcutBody i ++ [r] := by
  simp [LevelTree.serialize]

/--
When a parsed context focuses a shortcut node, its serialization factors with
the exact literal body s_i exposed.
-/
theorem levelTreeContext_shortcut_body_factor
    {n i : Nat}
    (ctx : LevelTreeContext n i) :
    (ctx.plug (.shortcut i)).serialize =
      (ctx.prefix ++ [l]) ++
        levelShortcutBody i ++
        ([r] ++ ctx.suffix) := by
  rw [levelTreeContext_serialize_plug]
  rw [shortcutLevelTree_serialize_eq_bracket_body]
  simp [List.append_assoc]

/--
The matching clean expansion exposes b_i in precisely the same external word
context.
-/
theorem levelTreeContext_clean_body_factor
    {n i : Nat}
    (ctx : LevelTreeContext n i) :
    (ctx.plug (cleanLevelTree i)).serialize =
      (ctx.prefix ++ [l]) ++
        levelCleanNodeBody i ++
        ([r] ++ ctx.suffix) := by
  rw [levelTreeContext_serialize_plug]
  rw [cleanLevelTree_serialize_eq_bracket_body]
  simp [List.append_assoc]

/-- One literal manuscript replacement s_i <-> b_i inside a word. -/
inductive LevelBodyToggleStep :
    Word LevelTreeSymbol →
      Word LevelTreeSymbol → Prop
  | expand
      (i : Nat)
      (p q : Word LevelTreeSymbol) :
      LevelBodyToggleStep
        (p ++ levelShortcutBody i ++ q)
        (p ++ levelCleanNodeBody i ++ q)
  | contract
      (i : Nat)
      (p q : Word LevelTreeSymbol) :
      LevelBodyToggleStep
        (p ++ levelCleanNodeBody i ++ q)
        (p ++ levelShortcutBody i ++ q)

/-- Literal body toggling is symmetric. -/
theorem levelBodyToggleStep_symm
    {x y : Word LevelTreeSymbol}
    (h : LevelBodyToggleStep x y) :
    LevelBodyToggleStep y x := by
  cases h with
  | expand i p q =>
      exact LevelBodyToggleStep.contract i p q
  | contract i p q =>
      exact LevelBodyToggleStep.expand i p q

/--
Every legal parsed-tree toggle is exactly one literal body replacement in the
serialized word.
-/
theorem levelTreeToggle_to_bodyToggleStep
    {n : Nat}
    {s t : LevelTree n}
    (h : LevelTreeToggle s t) :
    LevelBodyToggleStep s.serialize t.serialize := by
  cases h with
  | @expand i ctx =>
      rw [levelTreeContext_shortcut_body_factor,
        levelTreeContext_clean_body_factor]
      exact
        LevelBodyToggleStep.expand
          i (ctx.prefix ++ [l]) ([r] ++ ctx.suffix)
  | @contract i ctx =>
      rw [levelTreeContext_clean_body_factor,
        levelTreeContext_shortcut_body_factor]
      exact
        LevelBodyToggleStep.contract
          i (ctx.prefix ++ [l]) ([r] ++ ctx.suffix)

/-- Literal body replacement preserves the external word context. -/
theorem levelBodyToggleStep_contextual
    {x y : Word LevelTreeSymbol}
    (h : LevelBodyToggleStep x y)
    (u v : Word LevelTreeSymbol) :
    LevelBodyToggleStep
      (u ++ x ++ v)
      (u ++ y ++ v) := by
  cases h with
  | expand i p q =>
      simpa [List.append_assoc] using
        (LevelBodyToggleStep.expand
          i (u ++ p) (q ++ v))
  | contract i p q =>
      simpa [List.append_assoc] using
        (LevelBodyToggleStep.contract
          i (u ++ p) (q ++ v))

end TCS1
end LeanCfgProject
