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

end TCS1
end LeanCfgProject
