import LeanCfgProject.TCS1.V83LevelCodedTreeLanguage

/-!
# TCS #1 v83: direct semantics of the compact lower-bound grammars

This module mirrors the displayed grammar families R_n and R_n^- from the
current manuscript at the level of their named nonterminals Z_i, A_i and
A_i^-.

It proves:
* Z_i generates exactly 0^(i+1);
* A_i generates exactly the level-coded tree language T_i;
* A_i^- generates exactly the shortcut-containing language T_i^-;
* both A_i and A_i^- have an explicit shortcut yield of length i+5.

A later finite-CFG bridge will package these direct derivation relations into
the repository's generic indexed CFG representation and discharge
reachability/reducedness and the final presentation-size accounting.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Direct derivation semantics of Z_0 -> 0 and Z_(i+1) -> Z_i 0. -/
inductive LevelCodeZDerives : Nat → Word LevelTreeSymbol → Prop
  | zero :
      LevelCodeZDerives 0 [zero]
  | succ {i : Nat} {w : Word LevelTreeSymbol}
      (d : LevelCodeZDerives i w) :
      LevelCodeZDerives (i + 1) (w ++ [zero])

/-- Right-appending one zero realizes the successor replicate block. -/
@[simp] theorem replicate_zero_succ_right
    (i : Nat) :
    List.replicate (i + 1) zero =
      List.replicate i zero ++ [zero] := by
  calc
    List.replicate (i + 1) zero =
        List.replicate i zero ++
          List.replicate 1 zero := by
            rw [List.replicate_add]
    _ = List.replicate i zero ++ [zero] := by
          simp

/-- Every Z_i derivation is the intended zero block. -/
theorem levelCodeZDerives_shape
    {i : Nat} {w : Word LevelTreeSymbol}
    (d : LevelCodeZDerives i w) :
    w = List.replicate (i + 1) zero := by
  induction d with
  | zero =>
      simp
  | @succ i w d ih =>
      calc
        w ++ [zero] =
            List.replicate (i + 1) zero ++ [zero] := by
              rw [ih]
        _ = List.replicate ((i + 1) + 1) zero :=
          (replicate_zero_succ_right (i + 1)).symm

/-- The intended zero block is derivable from Z_i. -/
theorem levelCodeZDerives_replicate
    (i : Nat) :
    LevelCodeZDerives i
      (List.replicate (i + 1) zero) := by
  induction i with
  | zero =>
      simpa using LevelCodeZDerives.zero
  | succ i ih =>
      have h :
          LevelCodeZDerives (i + 1)
            (List.replicate (i + 1) zero ++ [zero]) :=
        LevelCodeZDerives.succ ih
      rw [show Nat.succ i + 1 = (i + 1) + 1 by omega,
        replicate_zero_succ_right (i + 1)]
      simpa [Nat.succ_eq_add_one] using h

/-- Direct semantics of the displayed A_i rules of R_n. -/
inductive LevelCodeADerives : Nat → Word LevelTreeSymbol → Prop
  | clean0 :
      LevelCodeADerives 0 [l, a, r]
  | shortcut {i : Nat} {z : Word LevelTreeSymbol}
      (dz : LevelCodeZDerives i z) :
      LevelCodeADerives i
        ([l, c] ++ z ++ [d, r])
  | node {i : Nat}
      {x y : Word LevelTreeSymbol}
      (dx : LevelCodeADerives i x)
      (dy : LevelCodeADerives i y) :
      LevelCodeADerives (i + 1)
        ([l] ++ x ++ y ++ [r])

/-- Every residual-height tree has a derivation from the matching A_i. -/
theorem levelTree_to_levelCodeADerives
    {i : Nat}
    (t : LevelTree i) :
    LevelCodeADerives i t.serialize := by
  induction t with
  | cleanLeaf =>
      simpa [LevelTree.serialize] using
        LevelCodeADerives.clean0
  | shortcut i =>
      have dz :=
        levelCodeZDerives_replicate i
      have h := LevelCodeADerives.shortcut dz
      simpa [LevelTree.serialize, levelShortcutBody,
        List.append_assoc] using h
  | @node i left right ihL ihR =>
      have h :=
        LevelCodeADerives.node ihL ihR
      simpa [LevelTree.serialize, List.append_assoc] using h

/-- Every A_i derivation serializes a residual-height-i tree. -/
theorem levelCodeADerives_to_language
    {i : Nat} {w : Word LevelTreeSymbol}
    (d : LevelCodeADerives i w) :
    w ∈ LevelTreeLanguage i := by
  induction d with
  | clean0 =>
      exact ⟨LevelTree.cleanLeaf, by
        simp [LevelTree.serialize]⟩
  | @shortcut i z dz =>
      have hz := levelCodeZDerives_shape dz
      refine ⟨LevelTree.shortcut i, ?_⟩
      rw [hz]
      simp [LevelTree.serialize, levelShortcutBody,
        List.append_assoc]
  | @node i x y dx dy ihX ihY =>
      rcases ihX with ⟨left, hleft⟩
      rcases ihY with ⟨right, hright⟩
      refine ⟨LevelTree.node left right, ?_⟩
      simp [LevelTree.serialize, hleft, hright,
        List.append_assoc]

/-- Exact generated language of A_i. -/
theorem levelCodeADerives_iff_language
    (i : Nat)
    (w : Word LevelTreeSymbol) :
    LevelCodeADerives i w ↔
      w ∈ LevelTreeLanguage i := by
  constructor
  · exact levelCodeADerives_to_language
  · rintro ⟨t, rfl⟩
    exact levelTree_to_levelCodeADerives t

/-- Start language of the displayed grammar R_n. -/
def LevelCodeRStartLanguage
    (n : Nat) :
    Set (Word LevelTreeSymbol) :=
  {w | LevelCodeADerives n w}

/-- The displayed R_n generates exactly T_n. -/
theorem levelCodeRStartLanguage_eq
    (n : Nat) :
    LevelCodeRStartLanguage n =
      LevelTreeLanguage n := by
  apply Set.ext
  intro w
  exact levelCodeADerives_iff_language n w

/-- Direct semantics of the displayed A_i^- rules of R_n^-. -/
inductive LevelCodeAMinusDerives :
    Nat → Word LevelTreeSymbol → Prop
  | shortcut {i : Nat} {z : Word LevelTreeSymbol}
      (dz : LevelCodeZDerives i z) :
      LevelCodeAMinusDerives i
        ([l, c] ++ z ++ [d, r])
  | nodeLeft {i : Nat}
      {x y : Word LevelTreeSymbol}
      (dx : LevelCodeAMinusDerives i x)
      (dy : LevelCodeADerives i y) :
      LevelCodeAMinusDerives (i + 1)
        ([l] ++ x ++ y ++ [r])
  | nodeRight {i : Nat}
      {x y : Word LevelTreeSymbol}
      (dx : LevelCodeADerives i x)
      (dy : LevelCodeAMinusDerives i y) :
      LevelCodeAMinusDerives (i + 1)
        ([l] ++ x ++ y ++ [r])

/-- Forgetting the minus mark gives an ordinary A_i derivation. -/
theorem levelCodeAMinusDerives_to_A
    {i : Nat} {w : Word LevelTreeSymbol}
    (d : LevelCodeAMinusDerives i w) :
    LevelCodeADerives i w := by
  induction d with
  | shortcut dz =>
      exact LevelCodeADerives.shortcut dz
  | nodeLeft dx dy ih =>
      exact LevelCodeADerives.node ih dy
  | nodeRight dx dy ih =>
      exact LevelCodeADerives.node dx ih

/-- Every minus derivation contains the distinguished shortcut letter c. -/
theorem levelCodeAMinusDerives_c_mem
    {i : Nat} {w : Word LevelTreeSymbol}
    (d : LevelCodeAMinusDerives i w) :
    c ∈ w := by
  induction d with
  | shortcut dz =>
      simp
  | nodeLeft dx dy ih =>
      simp [ih]
  | nodeRight dx dy ih =>
      simp [ih]

/-- Every A_i^- derivation lies in T_i^-. -/
theorem levelCodeAMinusDerives_to_shortcutLanguage
    {i : Nat} {w : Word LevelTreeSymbol}
    (d : LevelCodeAMinusDerives i w) :
    w ∈ LevelTreeShortcutLanguage i := by
  exact
    ⟨levelCodeADerives_to_language
        (levelCodeAMinusDerives_to_A d),
      levelCodeAMinusDerives_c_mem d⟩

/--
A parsed tree containing a shortcut has an A_i^- derivation.
-/
theorem levelTree_to_levelCodeAMinusDerives_of_hasShortcut
    {i : Nat}
    (t : LevelTree i)
    (h : t.HasShortcut) :
    LevelCodeAMinusDerives i t.serialize := by
  induction t with
  | cleanLeaf =>
      simp [LevelTree.HasShortcut] at h
  | shortcut i =>
      have dz := levelCodeZDerives_replicate i
      have d := LevelCodeAMinusDerives.shortcut dz
      simpa [LevelTree.serialize, levelShortcutBody,
        List.append_assoc] using d
  | @node i left right ihL ihR =>
      change left.HasShortcut ∨ right.HasShortcut at h
      rcases h with hL | hR
      · have dL := ihL hL
        have dR := levelTree_to_levelCodeADerives right
        have d := LevelCodeAMinusDerives.nodeLeft dL dR
        simpa [LevelTree.serialize, List.append_assoc] using d
      · have dL := levelTree_to_levelCodeADerives left
        have dR := ihR hR
        have d := LevelCodeAMinusDerives.nodeRight dL dR
        simpa [LevelTree.serialize, List.append_assoc] using d

/-- Exact generated language of A_i^-. -/
theorem levelCodeAMinusDerives_iff_shortcutLanguage
    (i : Nat)
    (w : Word LevelTreeSymbol) :
    LevelCodeAMinusDerives i w ↔
      w ∈ LevelTreeShortcutLanguage i := by
  constructor
  · exact levelCodeAMinusDerives_to_shortcutLanguage
  · rintro ⟨⟨t, rfl⟩, hc⟩
    have hs :
        t.HasShortcut :=
      (levelTree_c_mem_serialize_iff_hasShortcut t).1 hc
    exact
      levelTree_to_levelCodeAMinusDerives_of_hasShortcut
        t hs

/-- Start language of the displayed grammar R_n^-. -/
def LevelCodeRMinusStartLanguage
    (n : Nat) :
    Set (Word LevelTreeSymbol) :=
  {w | LevelCodeAMinusDerives n w}

/-- The displayed R_n^- generates exactly T_n^-. -/
theorem levelCodeRMinusStartLanguage_eq
    (n : Nat) :
    LevelCodeRMinusStartLanguage n =
      LevelTreeShortcutLanguage n := by
  apply Set.ext
  intro w
  exact levelCodeAMinusDerives_iff_shortcutLanguage n w

/-- Length of the explicit shortcut yield at residual height i. -/
theorem levelTree_shortcut_serialize_length
    (i : Nat) :
    (LevelTree.shortcut i).serialize.length = i + 5 := by
  simp [LevelTree.serialize, levelShortcutBody]

/-- Explicit short productive witness for A_i. -/
theorem levelCodeADerives_shortcut_witness
    (i : Nat) :
    ∃ w : Word LevelTreeSymbol,
      LevelCodeADerives i w ∧
      w.length ≤ i + 5 := by
  refine ⟨(LevelTree.shortcut i).serialize, ?_, ?_⟩
  · exact levelTree_to_levelCodeADerives
      (LevelTree.shortcut i)
  · rw [levelTree_shortcut_serialize_length]

/-- Explicit short productive witness for A_i^-. -/
theorem levelCodeAMinusDerives_shortcut_witness
    (i : Nat) :
    ∃ w : Word LevelTreeSymbol,
      LevelCodeAMinusDerives i w ∧
      w.length ≤ i + 5 := by
  refine ⟨(LevelTree.shortcut i).serialize, ?_, ?_⟩
  · have dz := levelCodeZDerives_replicate i
    have d := LevelCodeAMinusDerives.shortcut dz
    simpa [LevelTree.serialize, levelShortcutBody,
      List.append_assoc] using d
  · rw [levelTree_shortcut_serialize_length]

/--
Production-symbol count of the displayed R_n:
2 for S->A_n, 2 for Z_0->0, 3n for the remaining Z-rules,
10 for the two A_0 alternatives, and 11n for A_1,...,A_n.
-/
def levelCodeRProductionSymbolCount (n : Nat) : Nat :=
  14 * (n + 1)

theorem levelCodeRProductionSymbolCount_linear
    (n : Nat) :
    levelCodeRProductionSymbolCount n ≤
      14 * (n + 1) := by
  rfl

/--
For n>=1, the displayed R_n^- production-symbol count is 30n+9 under the
same "one LHS plus RHS symbols per production" convention.
-/
def levelCodeRMinusProductionSymbolCount (n : Nat) : Nat :=
  30 * n + 9

theorem levelCodeRMinusProductionSymbolCount_linear
    (n : Nat) :
    levelCodeRMinusProductionSymbolCount n ≤
      30 * (n + 1) + 9 := by
  unfold levelCodeRMinusProductionSymbolCount
  omega

end TCS1
end LeanCfgProject
