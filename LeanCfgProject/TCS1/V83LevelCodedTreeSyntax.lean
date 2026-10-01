import LeanCfgProject.TCS1.V83OrdinaryThicknessLowerBoundKernel

/-!
# TCS #1 v83: level-coded tree syntax

This module begins the end-to-end formalization of the ordinary-thickness
lower-bound family from the current manuscript.  It mirrors the Appendix
presentation after the level-coded tree proof was moved there.

We model exactly the six-letter alphabet, residual-height-indexed trees,
serialization, shortcut occurrence, and the unique clean serialization.
The Clark--Eyraud substitutability argument is developed in a subsequent
module.
-/

namespace LeanCfgProject
namespace TCS1

inductive LevelTreeSymbol where
  | l
  | r
  | a
  | c
  | zero
  | d
  deriving DecidableEq, Fintype, Repr

open LevelTreeSymbol

/-- The level-i shortcut body s_i = c 0^(i+1) d. -/
def levelShortcutBody (i : Nat) : Word LevelTreeSymbol :=
  c :: (List.replicate (i + 1) zero ++ [d])

@[simp] theorem levelShortcutBody_length
    (i : Nat) :
    (levelShortcutBody i).length = i + 3 := by
  simp [levelShortcutBody] <;> omega

/-- The zero run uniquely records the residual height of a shortcut. -/
theorem levelShortcutBody_injective :
    Function.Injective levelShortcutBody := by
  intro i j hij
  have hlen :=
    congrArg List.length hij
  simp only [levelShortcutBody_length] at hlen
  omega

/--
Residual-height-indexed parsed trees.

At height zero a node is either the clean a-leaf or a shortcut.
At positive height it is either a shortcut or an ordered binary node.
-/
inductive LevelTree : Nat → Type
  | cleanLeaf : LevelTree 0
  | shortcut (n : Nat) : LevelTree n
  | node {n : Nat} : LevelTree n → LevelTree n → LevelTree (n + 1)
  deriving Repr

/-- Serialization used in the manuscript. -/
def LevelTree.serialize : {n : Nat} → LevelTree n → Word LevelTreeSymbol
  | _, .cleanLeaf => [l, a, r]
  | _, .shortcut n => [l] ++ levelShortcutBody n ++ [r]
  | _, .node left right =>
      [l] ++ left.serialize ++ right.serialize ++ [r]

/-- The unique clean tree of residual height n. -/
def cleanLevelTree : (n : Nat) → LevelTree n
  | 0 => .cleanLeaf
  | n + 1 => .node (cleanLevelTree n) (cleanLevelTree n)

/-- The clean serialization z_n. -/
def cleanLevelTreeWord (n : Nat) : Word LevelTreeSymbol :=
  (cleanLevelTree n).serialize

/-- A parsed tree contains at least one shortcut node. -/
def LevelTree.HasShortcut : {n : Nat} → LevelTree n → Prop
  | _, .cleanLeaf => False
  | _, .shortcut _ => True
  | _, .node left right => left.HasShortcut ∨ right.HasShortcut

@[simp] theorem cleanLevelTree_hasShortcut_false
    (n : Nat) :
    ¬ (cleanLevelTree n).HasShortcut := by
  induction n with
  | zero =>
      simp [cleanLevelTree, LevelTree.HasShortcut]
  | succ n ih =>
      simp [cleanLevelTree, LevelTree.HasShortcut, ih]

/-- The distinguished letter c occurs in a serialization exactly at shortcuts. -/
theorem levelTree_c_mem_serialize_iff_hasShortcut
    {n : Nat}
    (t : LevelTree n) :
    c ∈ t.serialize ↔ t.HasShortcut := by
  induction t with
  | cleanLeaf =>
      simp [LevelTree.serialize, LevelTree.HasShortcut]
  | shortcut n =>
      simp [LevelTree.serialize, LevelTree.HasShortcut,
        levelShortcutBody]
  | @node n left right ihL ihR =>
      simp [LevelTree.serialize, LevelTree.HasShortcut, ihL, ihR]

/--
A shortcut-free parsed tree is the unique clean tree at its residual height.
-/
theorem levelTree_eq_clean_of_noShortcut
    {n : Nat}
    (t : LevelTree n)
    (h : ¬ t.HasShortcut) :
    t = cleanLevelTree n := by
  induction t with
  | cleanLeaf =>
      rfl
  | shortcut n =>
      simp [LevelTree.HasShortcut] at h
  | @node n left right ihL ihR =>
      have hL : ¬ left.HasShortcut := by
        intro hs
        exact h (Or.inl hs)
      have hR : ¬ right.HasShortcut := by
        intro hs
        exact h (Or.inr hs)
      rw [ihL hL, ihR hR]
      rfl

/-- Hence c-free serialization forces the clean word z_n. -/
theorem levelTree_serialize_eq_clean_of_c_not_mem
    {n : Nat}
    (t : LevelTree n)
    (h : c ∉ t.serialize) :
    t.serialize = cleanLevelTreeWord n := by
  have hNo : ¬ t.HasShortcut := by
    intro hs
    exact h ((levelTree_c_mem_serialize_iff_hasShortcut t).2 hs)
  rw [levelTree_eq_clean_of_noShortcut t hNo]
  rfl

/-- The finite level-coded tree language T_n, represented extensionally. -/
def LevelTreeLanguage (n : Nat) : Set (Word LevelTreeSymbol) :=
  {w | ∃ t : LevelTree n, t.serialize = w}

/-- The shortcut-containing sublanguage T_n^-. -/
def LevelTreeShortcutLanguage (n : Nat) : Set (Word LevelTreeSymbol) :=
  {w | w ∈ LevelTreeLanguage n ∧ c ∈ w}

/-- The clean word belongs to T_n. -/
theorem cleanLevelTreeWord_mem_language
    (n : Nat) :
    cleanLevelTreeWord n ∈ LevelTreeLanguage n := by
  exact ⟨cleanLevelTree n, rfl⟩

/-- The clean word contains no c. -/
theorem c_not_mem_cleanLevelTreeWord
    (n : Nat) :
    c ∉ cleanLevelTreeWord n := by
  intro hc
  have hs :
      (cleanLevelTree n).HasShortcut :=
    (levelTree_c_mem_serialize_iff_hasShortcut
      (cleanLevelTree n)).1 hc
  exact (cleanLevelTree_hasShortcut_false n) hs

/--
Exactly one word of T_n is shortcut-free: T_n \ T_n^- = {z_n}.
This is the set-theoretic difference used by the operator-independent
characteristic-sample obstruction.
-/
theorem levelTreeLanguage_diff_shortcut_eq_singleton
    (n : Nat) :
    LevelTreeLanguage n \ LevelTreeShortcutLanguage n =
      ({cleanLevelTreeWord n} : Set (Word LevelTreeSymbol)) := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨hLang, hNotShort⟩
    rcases hLang with ⟨t, rfl⟩
    have hc : c ∉ t.serialize := by
      intro hmem
      apply hNotShort
      exact ⟨⟨t, rfl⟩, hmem⟩
    have hz :=
      levelTree_serialize_eq_clean_of_c_not_mem t hc
    simpa [hz]
  · intro hw
    have hwEq : w = cleanLevelTreeWord n := by
      simpa using hw
    subst w
    refine ⟨cleanLevelTreeWord_mem_language n, ?_⟩
    intro hShort
    exact (c_not_mem_cleanLevelTreeWord n) hShort.2

/--
The shortcut-containing language is exactly the manuscript target
T_n \ {z_n}.
-/
theorem levelTreeShortcutLanguage_eq_diff_clean
    (n : Nat) :
    LevelTreeShortcutLanguage n =
      LevelTreeLanguage n \
        ({cleanLevelTreeWord n} :
          Set (Word LevelTreeSymbol)) := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨hLang, hc⟩
    refine ⟨hLang, ?_⟩
    intro hz
    have hw : w = cleanLevelTreeWord n := by
      simpa using hz
    subst w
    exact (c_not_mem_cleanLevelTreeWord n) hc
  · rintro ⟨hLang, hnotClean⟩
    refine ⟨hLang, ?_⟩
    by_contra hc
    push_neg at hc
    rcases hLang with ⟨t, rfl⟩
    have hz :
        t.serialize = cleanLevelTreeWord n :=
      levelTree_serialize_eq_clean_of_c_not_mem t hc
    apply hnotClean
    simpa [hz]

/-- Recursive length equation for the concrete clean serialization. -/
theorem cleanLevelTreeWord_length_rec
    (n : Nat) :
    (cleanLevelTreeWord n).length = levelCleanTreeLength n := by
  induction n with
  | zero =>
      simp [cleanLevelTreeWord, cleanLevelTree,
        LevelTree.serialize, levelCleanTreeLength]
  | succ n ih =>
      have ih' :
          (cleanLevelTree n).serialize.length =
            levelCleanTreeLength n := by
        simpa [cleanLevelTreeWord] using ih
      simp [cleanLevelTreeWord, cleanLevelTree,
        LevelTree.serialize, levelCleanTreeLength, ih'] <;>
        omega

/-- Concrete manuscript closed form |z_n| = 5*2^n-2. -/
theorem cleanLevelTreeWord_length
    (n : Nat) :
    (cleanLevelTreeWord n).length = 5 * 2^n - 2 := by
  rw [cleanLevelTreeWord_length_rec, levelCleanTreeLength_eq]

end TCS1
end LeanCfgProject
