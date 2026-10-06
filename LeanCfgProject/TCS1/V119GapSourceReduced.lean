import LeanCfgProject.TCS1.V119GapFiniteSSBNF
import Mathlib.Data.Fintype.Card

/-!
# TCS #1 v119: source reducedness of the finite gap family

This module proves all non-start symbols U,D,E_0,...,E_n are reachable
from the separated start in the *actual source production graph*, rather
than merely asserting the existence of a context in the ambient target.
Combining reachability with the already established one-letter productive
yield for each state certifies source reducedness. The finite family has
exactly n+3 non-start symbols. Finite production indexing and the
2n+7 total rule count are packaged in a separate module.
-/

namespace LeanCfgProject
namespace TCS1

/-- Source-production reachability from the separated start child. -/
inductive V119GapSourceReachable (n : Nat) :
    V119GapNT n → Prop
  | start {A : V119GapNT n}
      (hs : v119GapStart n A) :
      V119GapSourceReachable n A
  | left {A B C : V119GapNT n}
      (ha : V119GapSourceReachable n A)
      (hbin : v119GapBinary n A B C) :
      V119GapSourceReachable n B
  | right {A B C : V119GapNT n}
      (ha : V119GapSourceReachable n A)
      (hbin : v119GapBinary n A B C) :
      V119GapSourceReachable n C

/-- Descending the E_n -> E_(n-1) E_(n-1) spine reaches every E_i. -/
theorem v119Gap_source_E_reachable_distance (n : Nat) :
    ∀ (k : Nat) (hk : k ≤ n),
      V119GapSourceReachable n
        (.e (⟨n - k, by omega⟩ : Fin (n + 1))) := by
  intro k
  induction k with
  | zero =>
      intro _
      have hb :
          v119GapBinary n
            .u (.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) .d := by
        simp [v119GapBinary]
      simpa using
        (V119GapSourceReachable.left
          (V119GapSourceReachable.start
            (by simp [v119GapStart])) hb)
  | succ k ih =>
      intro hk
      have hprev : k ≤ n := by omega
      have hb :
          v119GapBinary n
            (.e (⟨n - k, by omega⟩ : Fin (n + 1)))
            (.e (⟨n - (k + 1), by omega⟩ : Fin (n + 1)))
            (.e (⟨n - (k + 1), by omega⟩ : Fin (n + 1))) := by
        change n - k = n - (k + 1) + 1 ∧
          n - (k + 1) = n - (k + 1)
        constructor <;> omega
      exact V119GapSourceReachable.left (ih hprev) hb

/-- Every non-start symbol is genuinely graph-reachable. -/
theorem v119Gap_all_source_reachable (n : Nat) :
    ∀ A : V119GapNT n,
      V119GapSourceReachable n A := by
  intro A
  cases A with
  | u =>
      exact V119GapSourceReachable.start
        (by simp [v119GapStart])
  | d =>
      have hb :
          v119GapBinary n
            .u (.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) .d := by
        simp [v119GapBinary]
      exact V119GapSourceReachable.right
        (V119GapSourceReachable.start
          (by simp [v119GapStart])) hb
  | e i =>
      have hi : i.val ≤ n := by omega
      have hk : n - i.val ≤ n := by omega
      have hreach :=
        v119Gap_source_E_reachable_distance
          n (n - i.val) hk
      have heq :
          (⟨n - (n - i.val), by omega⟩ : Fin (n + 1)) = i := by
        apply Fin.ext
        change n - (n - i.val) = i.val
        omega
      simpa only [heq] using hreach

/-- Each source non-start symbol is reachable and has a length-1 yield. -/
theorem v119Gap_source_reduced_certificate (n : Nat) :
    ∀ A : V119GapNT n,
      V119GapSourceReachable n A ∧
      ∃ w : Word V117GapLetter,
        UntypedDerives (v119GapTerminal n) (v119GapBinary n)
          A w ∧ w.length = 1 := by
  intro A
  exact ⟨v119Gap_all_source_reachable n A,
    v119Gap_all_source_short_yields n A⟩

/-- A useful concrete arithmetic presentation of the finite NT type. -/
abbrev V119GapNTCode (n : Nat) :=
  Unit ⊕ (Unit ⊕ Fin (n + 1))

def v119GapNTEquiv (n : Nat) :
    V119GapNT n ≃ V119GapNTCode n where
  toFun
    | .u => Sum.inl ()
    | .d => Sum.inr (Sum.inl ())
    | .e i => Sum.inr (Sum.inr i)
  invFun
    | Sum.inl _ => .u
    | Sum.inr (Sum.inl _) => .d
    | Sum.inr (Sum.inr i) => .e i
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    rcases x with _ | x
    · rfl
    rcases x with _ | _ <;> rfl

/-- Exact count n+3 of non-start symbols, including U and D. -/
theorem v119GapNT_card (n : Nat) :
    Fintype.card (V119GapNT n) = n + 3 := by
  calc
    Fintype.card (V119GapNT n) =
        Fintype.card (V119GapNTCode n) :=
      Fintype.card_congr (v119GapNTEquiv n)
    _ = n + 3 := by
      simp [V119GapNTCode]
      omega

end TCS1
end LeanCfgProject
