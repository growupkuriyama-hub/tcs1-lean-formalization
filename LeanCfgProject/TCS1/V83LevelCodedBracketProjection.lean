import LeanCfgProject.TCS1.V83LevelCodedTreeSyntax
import LeanCfgProject.TCS1.DyckOneBracketKernel

/-!
# TCS #1 v83: bracket projection of level-coded trees

The Appendix proof uses the fact that the letters l/r form matching tree
brackets, while shortcut bodies contain no brackets.  This module makes that
claim explicit by projecting level-coded words to the one-bracket Dyck
alphabet already formalized elsewhere in the TCS1 development.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Keep only l/r, sending them to the one-bracket Dyck alphabet. -/
def levelBracketLetter :
    LevelTreeSymbol → Option DyckOne.Symbol
  | l => some DyckOne.Symbol.a
  | r => some DyckOne.Symbol.b
  | _ => none

/-- Bracket projection of a level-coded word. -/
def levelBracketProjection
    (w : Word LevelTreeSymbol) :
    Word DyckOne.Symbol :=
  w.filterMap levelBracketLetter

@[simp] theorem levelBracketProjection_nil :
    levelBracketProjection [] = [] := by
  rfl

@[simp] theorem levelBracketProjection_append
    (u v : Word LevelTreeSymbol) :
    levelBracketProjection (u ++ v) =
      levelBracketProjection u ++
        levelBracketProjection v := by
  simp [levelBracketProjection]

@[simp] theorem levelBracketProjection_shortcutBody
    (i : Nat) :
    levelBracketProjection (levelShortcutBody i) = [] := by
  simp [levelBracketProjection, levelShortcutBody,
    levelBracketLetter]

/-- Concatenation closure of the already verified one-bracket Dyck language. -/
theorem dyckOne_append_mem
    {x y : Word DyckOne.Symbol}
    (hx : x ∈ DyckOne.Language)
    (hy : y ∈ DyckOne.Language) :
    x ++ y ∈ DyckOne.Language := by
  change DyckOne.scan 0 (x ++ y) = some 0
  rw [DyckOne.scan_append, hx]
  exact hy

/--
Every level-tree serialization projects to a balanced one-bracket Dyck word.
-/
theorem levelTree_bracketProjection_mem_dyck
    {n : Nat}
    (t : LevelTree n) :
    levelBracketProjection t.serialize ∈
      DyckOne.Language := by
  induction t with
  | cleanLeaf =>
      simp [LevelTree.serialize, levelBracketProjection,
        levelBracketLetter, DyckOne.Language, DyckOne.scan]
  | shortcut i =>
      simp [LevelTree.serialize,
        levelBracketProjection_append,
        levelBracketProjection_shortcutBody,
        levelBracketProjection, levelBracketLetter,
        DyckOne.Language, DyckOne.scan]
  | @node n left right ihL ihR =>
      have hinner :
          levelBracketProjection left.serialize ++
              levelBracketProjection right.serialize ∈
            DyckOne.Language :=
        dyckOne_append_mem ihL ihR
      change
        DyckOne.scan 0
          (levelBracketProjection
            (LevelTree.node left right).serialize) =
          some 0
      simp only [LevelTree.serialize,
        levelBracketProjection_append]
      change
        DyckOne.scan 0
          (DyckOne.Symbol.a ::
            (levelBracketProjection left.serialize ++
              levelBracketProjection right.serialize ++
                [DyckOne.Symbol.b])) =
          some 0
      simp only [DyckOne.scan]
      rw [DyckOne.scan_append]
      have hinner1 :
          DyckOne.scan 1
            (levelBracketProjection left.serialize ++
              levelBracketProjection right.serialize) =
            some 1 :=
        DyckOne.scan_dyck_at_height hinner 1
      rw [hinner1]
      simp [DyckOne.scan]

/--
At every ambient stack height, a serialized level tree is a neutral balanced
excursion after bracket projection.
-/
theorem levelTree_bracketProjection_neutral
    {n : Nat}
    (t : LevelTree n)
    (h : Nat) :
    DyckOne.scan h
        (levelBracketProjection t.serialize) =
      some h := by
  exact
    DyckOne.scan_dyck_at_height
      (levelTree_bracketProjection_mem_dyck t) h

/--
Shortcut serialization contributes exactly one matching bracket pair to the
projection, independently of its residual-height code.
-/
@[simp] theorem levelBracketProjection_shortcut_serialize
    (i : Nat) :
    levelBracketProjection
        (LevelTree.shortcut i).serialize =
      [DyckOne.Symbol.a, DyckOne.Symbol.b] := by
  simp [LevelTree.serialize, levelBracketProjection,
    levelBracketLetter, levelShortcutBody]

end TCS1
end LeanCfgProject
