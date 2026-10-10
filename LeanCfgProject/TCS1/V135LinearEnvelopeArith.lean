import Mathlib.Tactic.Ring

/-!
# TCS #1 v135: polynomial form of the linear characteristic-data envelope

Pure arithmetic used by `thm:main`(v) (`V135MainTheoremItemV.lean`).  The
verified linear envelope `indexedLinearCharacteristicEnvelope m n` unfolds to

  `(g·m + (g² + g³·m²) + 1) · (4·(g·m) + 1 + 1)`  with  `g = 2·(n + 2n² + 2n³)`,

and is dominated by `linEnvConst m · (n+1)^12`.
-/

namespace LeanCfgProject
namespace TCS1

/-- Constant of the degree-12 domination (depends only on `m = |M|`). -/
def linEnvConst (m : Nat) : Nat :=
  (10 * m + 100 + 1000 * m ^ 2 + 1) * (40 * m + 2)

theorem linEnvelope_unfolded_le_poly (m n : Nat) :
    (2 * (n + 2 * n ^ 2 + 2 * n ^ 3) * m +
        ((2 * (n + 2 * n ^ 2 + 2 * n ^ 3)) ^ 2 +
          (2 * (n + 2 * n ^ 2 + 2 * n ^ 3)) ^ 3 * m ^ 2) + 1) *
      (4 * (2 * (n + 2 * n ^ 2 + 2 * n ^ 3) * m) + 1 + 1)
      ≤ linEnvConst m * (n + 1) ^ 12 := by
  set Y := (n + 1) ^ 3 with hY
  have hY1 : 1 ≤ Y := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have h1 : n ≤ Y := by
    calc n ≤ n + 1 := Nat.le_succ n
      _ ≤ (n + 1) ^ 3 := Nat.le_self_pow (by omega) _
  have h2 : n ^ 2 ≤ Y := by
    calc n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (Nat.le_succ n) 2
      _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have h3 : n ^ 3 ≤ Y := Nat.pow_le_pow_left (Nat.le_succ n) 3
  set g := 2 * (n + 2 * n ^ 2 + 2 * n ^ 3) with hg
  have hgY : g ≤ 10 * Y := by omega
  have hg2 : g ^ 2 ≤ 100 * Y ^ 2 := by
    calc g ^ 2 ≤ (10 * Y) ^ 2 := Nat.pow_le_pow_left hgY 2
      _ = 100 * Y ^ 2 := by ring
  have hg3 : g ^ 3 ≤ 1000 * Y ^ 3 := by
    calc g ^ 3 ≤ (10 * Y) ^ 3 := Nat.pow_le_pow_left hgY 3
      _ = 1000 * Y ^ 3 := by ring
  have hY12 : Y ≤ Y ^ 3 := Nat.le_self_pow (by omega) _
  have hY23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by omega)
  have hY03 : 1 ≤ Y ^ 3 := Nat.one_le_pow _ _ hY1
  -- first factor ≤ A · Y³
  have hA : g * m + (g ^ 2 + g ^ 3 * m ^ 2) + 1 ≤
      (10 * m + 100 + 1000 * m ^ 2 + 1) * Y ^ 3 := by
    have a1 : g * m ≤ 10 * Y * m := Nat.mul_le_mul_right m hgY
    have a2 : g ^ 3 * m ^ 2 ≤ 1000 * Y ^ 3 * m ^ 2 := Nat.mul_le_mul_right _ hg3
    have a3 : 10 * Y * m ≤ 10 * Y ^ 3 * m :=
      Nat.mul_le_mul_right m (Nat.mul_le_mul_left 10 hY12)
    have e : (10 * m + 100 + 1000 * m ^ 2 + 1) * Y ^ 3 =
        10 * Y ^ 3 * m + 100 * Y ^ 3 + 1000 * Y ^ 3 * m ^ 2 + Y ^ 3 := by ring
    omega
  -- second factor ≤ B · Y
  have hB : 4 * (g * m) + 1 + 1 ≤ (40 * m + 2) * Y := by
    have b1 : g * m ≤ 10 * Y * m := Nat.mul_le_mul_right m hgY
    have e : (40 * m + 2) * Y = 40 * (Y * m) + 2 * Y := by ring
    have e2 : 10 * Y * m = 10 * (Y * m) := by ring
    omega
  calc (g * m + (g ^ 2 + g ^ 3 * m ^ 2) + 1) * (4 * (g * m) + 1 + 1)
      ≤ ((10 * m + 100 + 1000 * m ^ 2 + 1) * Y ^ 3) * ((40 * m + 2) * Y) :=
        Nat.mul_le_mul hA hB
    _ = linEnvConst m * (n + 1) ^ 12 := by
        rw [hY]; unfold linEnvConst; ring

end TCS1
end LeanCfgProject
