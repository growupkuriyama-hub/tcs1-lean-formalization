import Mathlib.Computability.MyhillNerode
import LeanCfgProject.TCS1.DeltaStarFixedH

/-!
# TCS #1 v78: nonregularity of Delta-star

The manuscript proves nonregularity from
  Delta* ∩ a* b* = { a^n b^n : n >= 0 }.
For the Lean development a direct Myhill--Nerode proof is shorter.  The left
quotients by a^n are pairwise distinct, with b^n as the distinguishing suffix.

This proof is independent of the fixed-h argument and uses only the exact
parser semantics already verified for the Delta-star language.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/-- Delta-star through Mathlib's formal-language API. -/
def FormalLanguage : _root_.Language Symbol :=
  { w | w ∈ Language }

@[simp] theorem mem_FormalLanguage
    (w : Word Symbol) :
    w ∈ FormalLanguage ↔
      w ∈ Language := by
  rfl

/-- A monotone block a^n b^m is accepted only when its exponents agree. -/
theorem block_exponents_eq_of_mem
    {n m : Nat}
    (hmem :
      List.replicate n a ++
          List.replicate m b ∈ Language) :
    n = m := by
  have hzero := balance_mem_zero hmem
  simp only [balance_append,
    balance_replicate_a,
    balance_replicate_b] at hzero
  omega

/-- The left quotients by a^n are pairwise distinct. -/
theorem leftQuotient_prefix_injective :
    Function.Injective
      (fun n : Nat =>
        FormalLanguage.leftQuotient
          (List.replicate n a)) := by
  intro m n hmn
  let suffix : Word Symbol :=
    List.replicate m b
  have hm :
      suffix ∈
        FormalLanguage.leftQuotient
          (List.replicate m a) := by
    change
      List.replicate m a ++
          List.replicate m b ∈ Language
    exact block_mem m
  have hmn' :
      FormalLanguage.leftQuotient
          (List.replicate m a) =
        FormalLanguage.leftQuotient
          (List.replicate n a) := by
    simpa using hmn
  have hn :
      suffix ∈
        FormalLanguage.leftQuotient
          (List.replicate n a) := by
    rw [← hmn']
    exact hm
  have hnFormal :
      List.replicate n a ++ suffix ∈
        FormalLanguage := by
    exact hn
  have hnSet :
      List.replicate n a ++ suffix ∈ Language :=
    (mem_FormalLanguage
      (List.replicate n a ++ suffix)).1
      hnFormal
  have hnm : n = m :=
    block_exponents_eq_of_mem
      (by simpa [suffix] using hnSet)
  exact hnm.symm

/-- Nonregularity component of Proposition 9.1. -/
theorem not_regular :
    ¬ FormalLanguage.IsRegular := by
  intro hreg
  have hfinite :
      (Set.range FormalLanguage.leftQuotient).Finite :=
    (Language.isRegular_iff_finite_range_leftQuotient).1
      hreg
  have hinfinite :
      (Set.range
        (fun n : Nat =>
          FormalLanguage.leftQuotient
            (List.replicate n a))).Infinite :=
    Set.infinite_range_of_injective
      leftQuotient_prefix_injective
  have hsubset :
      Set.range
          (fun n : Nat =>
            FormalLanguage.leftQuotient
              (List.replicate n a))
        ⊆
      Set.range FormalLanguage.leftQuotient := by
    rintro q ⟨n, rfl⟩
    exact ⟨List.replicate n a, rfl⟩
  exact hinfinite (hfinite.subset hsubset)

end DeltaStar
end TCS1
end LeanCfgProject
