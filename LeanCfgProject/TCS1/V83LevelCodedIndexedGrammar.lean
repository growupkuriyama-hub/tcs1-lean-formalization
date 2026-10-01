import LeanCfgProject.TCS1.FiniteCFGEncoding
import LeanCfgProject.TCS1.V83LevelCodedDisplayedGrammar

/-!
# TCS #1 v83: finite indexed presentation of the compact grammar R_n

The manuscript's ordinary-thickness lower bound displays a concrete finite CFG

  S -> A_n
  Z_0 -> 0
  Z_i -> Z_(i-1) 0
  A_0 -> l a r | l c Z_0 d r
  A_i -> l A_(i-1) A_(i-1) r | l c Z_i d r.

This module packages that displayed grammar as an actual finite indexed mixed
CFG.  The direct derivation semantics and exact target-language proofs remain
in V83LevelCodedDisplayedGrammar; a subsequent bridge relates the two
presentations.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Embed an index below n into the index type below n+1. -/
def levelCodeFinEmbed {n : Nat} (i : Fin n) :
    Fin (n + 1) :=
  ⟨i.1, lt_trans i.2 (Nat.lt_succ_self n)⟩

/-- Successor index below n+1. -/
def levelCodeFinSucc {n : Nat} (i : Fin n) :
    Fin (n + 1) :=
  ⟨i.1 + 1, by omega⟩

/-- Zero index below n+1. -/
def levelCodeFinZero (n : Nat) :
    Fin (n + 1) :=
  ⟨0, by omega⟩

/-- Top index n below n+1. -/
def levelCodeFinTop (n : Nat) :
    Fin (n + 1) :=
  ⟨n, by omega⟩

/-- Nonterminals of the displayed R_n, including the start symbol. -/
inductive LevelCodeRNT (n : Nat) where
  | start
  | z (i : Fin (n + 1))
  | a (i : Fin (n + 1))
  deriving DecidableEq, Fintype, Repr

/-- Production indices of the displayed R_n. -/
inductive LevelCodeRProd (n : Nat) where
  | start
  | z0
  | zSucc (i : Fin n)
  | a0Clean
  | aShortcut (i : Fin (n + 1))
  | aNode (i : Fin n)
  deriving DecidableEq, Fintype, Repr

/-- Actual finite indexed mixed CFG R_n. -/
def levelCodeRIndexedGrammar
    (n : Nat) :
    IndexedMixedCFG
      (LevelCodeRNT n)
      LevelTreeSymbol
      (LevelCodeRProd n) where
  lhs
    | .start => .start
    | .z0 => .z (levelCodeFinZero n)
    | .zSucc i => .z (levelCodeFinSucc i)
    | .a0Clean => .a (levelCodeFinZero n)
    | .aShortcut i => .a i
    | .aNode i => .a (levelCodeFinSucc i)
  rhs
    | .start =>
        [Sum.inl (.a (levelCodeFinTop n))]
    | .z0 =>
        [Sum.inr zero]
    | .zSucc i =>
        [Sum.inl (.z (levelCodeFinEmbed i)),
          Sum.inr zero]
    | .a0Clean =>
        [Sum.inr l, Sum.inr a, Sum.inr r]
    | .aShortcut i =>
        [Sum.inr l, Sum.inr c,
          Sum.inl (.z i),
          Sum.inr d, Sum.inr r]
    | .aNode i =>
        [Sum.inr l,
          Sum.inl (.a (levelCodeFinEmbed i)),
          Sum.inl (.a (levelCodeFinEmbed i)),
          Sum.inr r]

/-- Every R_n right-hand side has length at most five. -/
theorem levelCodeRIndexed_rhs_length_le_five
    (n : Nat)
    (p : LevelCodeRProd n) :
    ((levelCodeRIndexedGrammar n).rhs p).length ≤ 5 := by
  cases p <;> simp [levelCodeRIndexedGrammar]

/-- The indexed start production is exactly S -> A_n. -/
@[simp] theorem levelCodeRIndexed_start_rhs
    (n : Nat) :
    (levelCodeRIndexedGrammar n).rhs
        (LevelCodeRProd.start) =
      [Sum.inl
        (LevelCodeRNT.a (levelCodeFinTop n))] := by
  rfl

/-- The indexed Z_0 production is exactly Z_0 -> 0. -/
@[simp] theorem levelCodeRIndexed_z0_rhs
    (n : Nat) :
    (levelCodeRIndexedGrammar n).rhs
        (LevelCodeRProd.z0) =
      [Sum.inr zero] := by
  rfl


/--
Nonterminals of R_(m+1)^-.  The ordinary A_i symbols are indexed by
i < m+1, while A_i^- and Z_i run through i <= m+1.
-/
inductive LevelCodeRMinusNT (m : Nat) where
  | start
  | z (i : Fin (m + 2))
  | a (i : Fin (m + 1))
  | am (i : Fin (m + 2))
  deriving DecidableEq, Fintype, Repr

/-- Production indices of the displayed R_(m+1)^-. -/
inductive LevelCodeRMinusProd (m : Nat) where
  | start
  | z0
  | zSucc (i : Fin (m + 1))
  | a0Clean
  | aShortcut (i : Fin (m + 1))
  | aNode (i : Fin m)
  | amShortcut (i : Fin (m + 2))
  | amNodeLeft (i : Fin (m + 1))
  | amNodeRight (i : Fin (m + 1))
  deriving DecidableEq, Fintype, Repr

/-- Actual finite indexed mixed CFG R_(m+1)^-. -/
def levelCodeRMinusIndexedGrammar
    (m : Nat) :
    IndexedMixedCFG
      (LevelCodeRMinusNT m)
      LevelTreeSymbol
      (LevelCodeRMinusProd m) where
  lhs
    | .start =>
        .start
    | .z0 =>
        .z (levelCodeFinZero (m + 1))
    | .zSucc i =>
        .z (levelCodeFinSucc i)
    | .a0Clean =>
        .a (levelCodeFinZero m)
    | .aShortcut i =>
        .a i
    | .aNode i =>
        .a (levelCodeFinSucc i)
    | .amShortcut i =>
        .am i
    | .amNodeLeft i =>
        .am (levelCodeFinSucc i)
    | .amNodeRight i =>
        .am (levelCodeFinSucc i)
  rhs
    | .start =>
        [Sum.inl
          (.am (levelCodeFinTop (m + 1)))]
    | .z0 =>
        [Sum.inr zero]
    | .zSucc i =>
        [Sum.inl
          (.z (levelCodeFinEmbed i)),
          Sum.inr zero]
    | .a0Clean =>
        [Sum.inr l, Sum.inr a, Sum.inr r]
    | .aShortcut i =>
        [Sum.inr l, Sum.inr c,
          Sum.inl
            (.z (levelCodeFinEmbed i)),
          Sum.inr d, Sum.inr r]
    | .aNode i =>
        [Sum.inr l,
          Sum.inl
            (.a (levelCodeFinEmbed i)),
          Sum.inl
            (.a (levelCodeFinEmbed i)),
          Sum.inr r]
    | .amShortcut i =>
        [Sum.inr l, Sum.inr c,
          Sum.inl (.z i),
          Sum.inr d, Sum.inr r]
    | .amNodeLeft i =>
        [Sum.inr l,
          Sum.inl
            (.am (levelCodeFinEmbed i)),
          Sum.inl (.a i),
          Sum.inr r]
    | .amNodeRight i =>
        [Sum.inr l,
          Sum.inl (.a i),
          Sum.inl
            (.am (levelCodeFinEmbed i)),
          Sum.inr r]

/-- Every R_(m+1)^- right-hand side has length at most five. -/
theorem levelCodeRMinusIndexed_rhs_length_le_five
    (m : Nat)
    (p : LevelCodeRMinusProd m) :
    ((levelCodeRMinusIndexedGrammar m).rhs p).length ≤ 5 := by
  cases p <;> simp [levelCodeRMinusIndexedGrammar]

/-- The indexed minus start production is S^- -> A^-_(m+1). -/
@[simp] theorem levelCodeRMinusIndexed_start_rhs
    (m : Nat) :
    (levelCodeRMinusIndexedGrammar m).rhs
        (LevelCodeRMinusProd.start) =
      [Sum.inl
        (LevelCodeRMinusNT.am
          (levelCodeFinTop (m + 1)))] := by
  rfl

end TCS1
end LeanCfgProject
