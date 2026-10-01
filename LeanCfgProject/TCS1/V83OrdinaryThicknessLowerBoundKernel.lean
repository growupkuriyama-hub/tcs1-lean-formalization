import LeanCfgProject.TCS1.SetDrivenCharacteristicObstruction
import LeanCfgProject.TCS1.SingletonDataLowerBound

/-!
# TCS #1 v83: operator-independent lower-bound kernel

This file isolates the representation-independent core of the new v83
ordinary-thickness lower bound.  If two nested targets differ by one long
word and the same set-driven operator has characteristic samples for both,
every characteristic sample for the larger target must contain that word.

The concrete level-coded tree family is developed separately.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section V83OrdinaryThicknessLowerBoundKernel

/--
Singleton-difference specialization of the nested-target obstruction.
-/
theorem singletonDifference_characteristicSample_contains
    {α : Type u}
    [DecidableEq α]
    (B : Finset (Word α) → Set (Word α))
    {L' L : Set (Word α)}
    {z : Word α}
    (hsub : L' ⊆ L)
    (hdiff : L \ L' = ({z} : Set (Word α)))
    {C C' : Finset (Word α)}
    (hC : IsSetDrivenCharacteristicSample B L C)
    (hC' : IsSetDrivenCharacteristicSample B L' C') :
    z ∈ C := by
  have hne : L' ≠ L := by
    intro heq
    have hempty : L \ L' = (∅ : Set (Word α)) := by
      rw [heq]
      simp
    rw [hdiff] at hempty
    have hz : z ∈ ({z} : Set (Word α)) := by simp
    rw [hempty] at hz
    exact hz
  obtain ⟨w, hwC, hwDiff⟩ :=
    nestedTarget_characteristicSample_obstruction
      B hsub hne hC hC'
  have hwz : w = z := by
    have hwSingleton : w ∈ ({z} : Set (Word α)) := by
      rw [← hdiff]
      exact hwDiff
    simpa using hwSingleton
  simpa [hwz] using hwC

/--
Every such characteristic sample pays at least the encoded length of the
unique distinguishing word.
-/
theorem singletonDifference_characteristicSample_norm_ge
    {α : Type u}
    [DecidableEq α]
    (B : Finset (Word α) → Set (Word α))
    {L' L : Set (Word α)}
    {z : Word α}
    (hsub : L' ⊆ L)
    (hdiff : L \ L' = ({z} : Set (Word α)))
    {C C' : Finset (Word α)}
    (hC : IsSetDrivenCharacteristicSample B L C)
    (hC' : IsSetDrivenCharacteristicSample B L' C') :
    z.length + 1 ≤ reconstructionSampleNorm C := by
  exact
    member_encoding_le_reconstructionSampleNorm C
      (singletonDifference_characteristicSample_contains
        B hsub hdiff hC hC')

/-- Length recurrence of the unique clean level-coded tree word. -/
def levelCleanTreeLength : Nat → Nat
  | 0 => 3
  | n + 1 => 2 + 2 * levelCleanTreeLength n

/-- Closed form used in the v83 lower bound: |z_n| = 5*2^n - 2. -/
theorem levelCleanTreeLength_eq
    (n : Nat) :
    levelCleanTreeLength n = 5 * 2^n - 2 := by
  induction n with
  | zero =>
      simp [levelCleanTreeLength]
  | succ n ih =>
      simp only [levelCleanTreeLength, ih, pow_succ]
      have hpow : 2 ≤ 5 * 2^n := by
        have hpos : 1 ≤ 2^n := by
          have hpos : 0 < 2 ^ n := by positivity
      omega
        omega
      omega

/--
If the distinguishing clean word has the level-n length, the generic
set-driven obstruction yields the manuscript's exponential norm lower bound.
-/
theorem levelCleanTree_characteristicSample_norm_ge
    {α : Type u}
    [DecidableEq α]
    (B : Finset (Word α) → Set (Word α))
    {L' L : Set (Word α)}
    {z : Word α}
    (n : Nat)
    (hzlen : z.length = levelCleanTreeLength n)
    (hsub : L' ⊆ L)
    (hdiff : L \ L' = ({z} : Set (Word α)))
    {C C' : Finset (Word α)}
    (hC : IsSetDrivenCharacteristicSample B L C)
    (hC' : IsSetDrivenCharacteristicSample B L' C') :
    5 * 2^n - 1 ≤ reconstructionSampleNorm C := by
  have h :=
    singletonDifference_characteristicSample_norm_ge
      B hsub hdiff hC hC'
  rw [hzlen, levelCleanTreeLength_eq] at h
  have hpow : 2 ≤ 5 * 2^n := by
    have hpos : 1 ≤ 2^n := by
      exact Nat.one_le_pow n (by omega)
    omega
  omega

end V83OrdinaryThicknessLowerBoundKernel

end TCS1
end LeanCfgProject
