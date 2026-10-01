import LeanCfgProject.TCS1.V83LevelCodedTreeSyntax

/-!
# TCS #1 v83: recursive presentation of the level-coded languages

The manuscript defines T_0 and T_{n+1} recursively before switching to the
tree view in the Appendix.  This file proves that the indexed tree
serialization model used by the Lean development is exactly that recursive
language definition.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Literal recursive definition of the manuscript's finite languages T_n. -/
def RecursiveLevelTreeLanguage :
    Nat → Set (Word LevelTreeSymbol)
  | 0 =>
      {w |
        [l, a, r] = w ∨
          ([l] ++ levelShortcutBody 0 ++ [r]) = w}
  | n + 1 =>
      {w |
        ([l] ++ levelShortcutBody (n + 1) ++ [r]) = w ∨
        ∃ x y : Word LevelTreeSymbol,
          x ∈ RecursiveLevelTreeLanguage n ∧
          y ∈ RecursiveLevelTreeLanguage n ∧
          ([l] ++ x ++ y ++ [r]) = w}

/--
The recursive language definition and the residual-height tree serialization
definition coincide at every level.
-/
theorem recursiveLevelTreeLanguage_eq
    (n : Nat) :
    RecursiveLevelTreeLanguage n =
      LevelTreeLanguage n := by
  induction n with
  | zero =>
      apply Set.ext
      intro w
      constructor
      · intro hw
        rcases hw with hclean | hshortcut
        · refine ⟨LevelTree.cleanLeaf, ?_⟩
          simpa [LevelTree.serialize] using hclean
        · refine ⟨LevelTree.shortcut 0, ?_⟩
          simpa [LevelTree.serialize] using hshortcut
      · rintro ⟨t, rfl⟩
        cases t with
        | cleanLeaf =>
            exact Or.inl (by simp [LevelTree.serialize])
        | shortcut n =>
            exact Or.inr (by simp [LevelTree.serialize])
  | succ n ih =>
      apply Set.ext
      intro w
      constructor
      · intro hw
        rcases hw with hshortcut | hnode
        · refine ⟨LevelTree.shortcut (n + 1), ?_⟩
          simpa [LevelTree.serialize] using hshortcut
        · rcases hnode with ⟨x, y, hx, hy, hxy⟩
          have hx' : x ∈ LevelTreeLanguage n := by
            rw [← ih]
            exact hx
          have hy' : y ∈ LevelTreeLanguage n := by
            rw [← ih]
            exact hy
          rcases hx' with ⟨left, hleft⟩
          rcases hy' with ⟨right, hright⟩
          refine ⟨LevelTree.node left right, ?_⟩
          simpa [LevelTree.serialize, hleft, hright] using hxy
      · rintro ⟨t, rfl⟩
        cases t with
        | shortcut m =>
            exact Or.inl (by simp [LevelTree.serialize])
        | @node m left right =>
            right
            refine
              ⟨left.serialize, right.serialize, ?_, ?_, ?_⟩
            · rw [ih]
              exact ⟨left, rfl⟩
            · rw [ih]
              exact ⟨right, rfl⟩
            · simp [LevelTree.serialize]

end TCS1
end LeanCfgProject
