import LeanCfgProject.TCS1.V83LevelCodedIndexedReducedness
import LeanCfgProject.TCS1.FiniteCFGEncoding
import Mathlib.Data.Fintype.Card

/-!
# TCS #1 v83: linear finite-presentation size of the compact grammars

This module closes the representation-size bookkeeping for the two concrete
indexed grammars used in the ordinary-thickness lower bound.  We count the
finite state/production types explicitly and use the uniform RHS-length bound
to obtain a linear bound on the repository's concrete encoding scale.
-/

namespace LeanCfgProject
namespace TCS1

open scoped BigOperators

/-- Uniformly bounded right-hand sides give a linear total RHS count. -/
theorem indexedMixed_totalRhsLength_le_five_card
    {N α P : Type}
    [Fintype P]
    (G : IndexedMixedCFG N α P)
    (h : ∀ p : P, (G.rhs p).length ≤ 5) :
    G.totalRhsLength ≤ 5 * Fintype.card P := by
  unfold IndexedMixedCFG.totalRhsLength
  calc
    (∑ p : P, (G.rhs p).length)
        ≤ ∑ _p : P, 5 := by
          exact Finset.sum_le_sum
            (fun p _hp => h p)
    _ = Fintype.card P * 5 := by
      simp
    _ = 5 * Fintype.card P := by
      omega

abbrev LevelCodeRNTCode (n : Nat) :=
  Unit ⊕ (Fin (n + 1) ⊕ Fin (n + 1))

def levelCodeRNTEquiv
    (n : Nat) :
    LevelCodeRNT n ≃ LevelCodeRNTCode n where
  toFun
    | .start => Sum.inl ()
    | .z i => Sum.inr (Sum.inl i)
    | .a i => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl _ => .start
    | Sum.inr (Sum.inl i) => .z i
    | Sum.inr (Sum.inr i) => .a i
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    rcases x with _ | x
    · rfl
    · rcases x with _ | _ <;> rfl

/-- Exact number of nonterminals in R_n. -/
theorem levelCodeRNT_card
    (n : Nat) :
    Fintype.card (LevelCodeRNT n) =
      2 * n + 3 := by
  calc
    Fintype.card (LevelCodeRNT n) =
        Fintype.card (LevelCodeRNTCode n) :=
      Fintype.card_congr (levelCodeRNTEquiv n)
    _ = 2 * n + 3 := by
      simp [LevelCodeRNTCode]
      omega

abbrev LevelCodeRProdCode (n : Nat) :=
  Unit ⊕
    (Unit ⊕
      (Fin n ⊕
        (Unit ⊕
          (Fin (n + 1) ⊕ Fin n))))

def levelCodeRProdEquiv
    (n : Nat) :
    LevelCodeRProd n ≃ LevelCodeRProdCode n where
  toFun
    | .start => Sum.inl ()
    | .z0 => Sum.inr (Sum.inl ())
    | .zSucc i =>
        Sum.inr (Sum.inr (Sum.inl i))
    | .a0Clean =>
        Sum.inr (Sum.inr (Sum.inr (Sum.inl ())))
    | .aShortcut i =>
        Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr (Sum.inl i))))
    | .aNode i =>
        Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr (Sum.inr i))))
  invFun
    | Sum.inl _ => .start
    | Sum.inr (Sum.inl _) => .z0
    | Sum.inr (Sum.inr (Sum.inl i)) => .zSucc i
    | Sum.inr
        (Sum.inr (Sum.inr (Sum.inl _))) =>
          .a0Clean
    | Sum.inr
        (Sum.inr
          (Sum.inr
            (Sum.inr (Sum.inl i)))) =>
          .aShortcut i
    | Sum.inr
        (Sum.inr
          (Sum.inr
            (Sum.inr (Sum.inr i)))) =>
          .aNode i
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | _ <;> rfl

/-- Exact number of productions in R_n. -/
theorem levelCodeRProd_card
    (n : Nat) :
    Fintype.card (LevelCodeRProd n) =
      3 * n + 4 := by
  calc
    Fintype.card (LevelCodeRProd n) =
        Fintype.card (LevelCodeRProdCode n) :=
      Fintype.card_congr (levelCodeRProdEquiv n)
    _ = 3 * n + 4 := by
      simp [LevelCodeRProdCode]
      omega

/-- The concrete indexed encoding of R_n has linear size. -/
theorem levelCodeRIndexed_encodingScale_linear
    (n : Nat) :
    (levelCodeRIndexedGrammar n).encodingScale
      ≤ 20 * n + 27 := by
  have hRhs :
      (levelCodeRIndexedGrammar n).totalRhsLength
        ≤ 5 * Fintype.card (LevelCodeRProd n) :=
    indexedMixed_totalRhsLength_le_five_card
      (levelCodeRIndexedGrammar n)
      (levelCodeRIndexed_rhs_length_le_five n)
  unfold IndexedMixedCFG.encodingScale
  rw [levelCodeRNT_card, levelCodeRProd_card]
  omega

abbrev LevelCodeRMinusNTCode (m : Nat) :=
  Unit ⊕
    (Fin (m + 2) ⊕
      (Fin (m + 1) ⊕ Fin (m + 2)))

def levelCodeRMinusNTEquiv
    (m : Nat) :
    LevelCodeRMinusNT m ≃
      LevelCodeRMinusNTCode m where
  toFun
    | .start => Sum.inl ()
    | .z i => Sum.inr (Sum.inl i)
    | .a i =>
        Sum.inr (Sum.inr (Sum.inl i))
    | .am i =>
        Sum.inr (Sum.inr (Sum.inr i))
  invFun
    | Sum.inl _ => .start
    | Sum.inr (Sum.inl i) => .z i
    | Sum.inr (Sum.inr (Sum.inl i)) => .a i
    | Sum.inr (Sum.inr (Sum.inr i)) => .am i
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | _ <;> rfl

/-- Exact number of nonterminals in R_(m+1)^-. -/
theorem levelCodeRMinusNT_card
    (m : Nat) :
    Fintype.card (LevelCodeRMinusNT m) =
      3 * m + 6 := by
  calc
    Fintype.card (LevelCodeRMinusNT m) =
        Fintype.card (LevelCodeRMinusNTCode m) :=
      Fintype.card_congr (levelCodeRMinusNTEquiv m)
    _ = 3 * m + 6 := by
      simp [LevelCodeRMinusNTCode]
      omega

abbrev LevelCodeRMinusProdCode (m : Nat) :=
  Unit ⊕
    (Unit ⊕
      (Fin (m + 1) ⊕
        (Unit ⊕
          (Fin (m + 1) ⊕
            (Fin m ⊕
              (Fin (m + 2) ⊕
                (Fin (m + 1) ⊕
                  Fin (m + 1))))))))

def levelCodeRMinusProdEquiv
    (m : Nat) :
    LevelCodeRMinusProd m ≃
      LevelCodeRMinusProdCode m where
  toFun
    | .start => Sum.inl ()
    | .z0 => Sum.inr (Sum.inl ())
    | .zSucc i =>
        Sum.inr (Sum.inr (Sum.inl i))
    | .a0Clean =>
        Sum.inr
          (Sum.inr
            (Sum.inr (Sum.inl ())))
    | .aShortcut i =>
        Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr (Sum.inl i))))
    | .aNode i =>
        Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr
                (Sum.inr (Sum.inl i)))))
    | .amShortcut i =>
        Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr
                (Sum.inr
                  (Sum.inr (Sum.inl i))))))
    | .amNodeLeft i =>
        Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr
                (Sum.inr
                  (Sum.inr
                    (Sum.inr (Sum.inl i)))))))
    | .amNodeRight i =>
        Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr
                (Sum.inr
                  (Sum.inr
                    (Sum.inr
                      (Sum.inr i)))))))
  invFun
    | Sum.inl _ => .start
    | Sum.inr (Sum.inl _) => .z0
    | Sum.inr (Sum.inr (Sum.inl i)) => .zSucc i
    | Sum.inr
        (Sum.inr
          (Sum.inr (Sum.inl _))) =>
          .a0Clean
    | Sum.inr
        (Sum.inr
          (Sum.inr
            (Sum.inr (Sum.inl i)))) =>
          .aShortcut i
    | Sum.inr
        (Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr (Sum.inl i))))) =>
          .aNode i
    | Sum.inr
        (Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr
                (Sum.inr (Sum.inl i)))))) =>
          .amShortcut i
    | Sum.inr
        (Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr
                (Sum.inr
                  (Sum.inr (Sum.inl i))))))) =>
          .amNodeLeft i
    | Sum.inr
        (Sum.inr
          (Sum.inr
            (Sum.inr
              (Sum.inr
                (Sum.inr
                  (Sum.inr
                    (Sum.inr i))))))) =>
          .amNodeRight i
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | x
    · rfl
    rcases x with _ | _ <;> rfl

/-- Exact number of productions in R_(m+1)^-. -/
theorem levelCodeRMinusProd_card
    (m : Nat) :
    Fintype.card (LevelCodeRMinusProd m) =
      6 * m + 9 := by
  calc
    Fintype.card (LevelCodeRMinusProd m) =
        Fintype.card (LevelCodeRMinusProdCode m) :=
      Fintype.card_congr (levelCodeRMinusProdEquiv m)
    _ = 6 * m + 9 := by
      simp [LevelCodeRMinusProdCode]
      omega

/-- The concrete indexed encoding of R_(m+1)^- has linear size. -/
theorem levelCodeRMinusIndexed_encodingScale_linear
    (m : Nat) :
    (levelCodeRMinusIndexedGrammar m).encodingScale
      ≤ 39 * m + 60 := by
  have hRhs :
      (levelCodeRMinusIndexedGrammar m).totalRhsLength
        ≤ 5 * Fintype.card (LevelCodeRMinusProd m) :=
    indexedMixed_totalRhsLength_le_five_card
      (levelCodeRMinusIndexedGrammar m)
      (levelCodeRMinusIndexed_rhs_length_le_five m)
  unfold IndexedMixedCFG.encodingScale
  rw [levelCodeRMinusNT_card,
      levelCodeRMinusProd_card]
  omega

/-- Joint linear size bound for R_(m+1) and R_(m+1)^-. -/
theorem levelCodeIndexed_encodingScale_joint_linear
    (m : Nat) :
    (levelCodeRIndexedGrammar (m + 1)).encodingScale +
        (levelCodeRMinusIndexedGrammar m).encodingScale
      ≤ 59 * (m + 1) + 48 := by
  have hR :=
    levelCodeRIndexed_encodingScale_linear (m + 1)
  have hM :=
    levelCodeRMinusIndexed_encodingScale_linear m
  omega

end TCS1
end LeanCfgProject
