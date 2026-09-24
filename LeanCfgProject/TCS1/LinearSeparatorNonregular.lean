import Mathlib.Computability.MyhillNerode
import LeanCfgProject.TCS1.LinearSeparatorDistribution

/-!
# TCS #1 v78: nonregularity of L_{±,e}

The manuscript proves nonregularity by intersecting with a^* e b^*.  Here we
use an equivalent direct Myhill--Nerode argument that is particularly compact
in Lean: the left quotients by a^n are pairwise distinct, witnessed by the
suffix e b^n.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- L_{±,e} viewed through Mathlib's formal-language API. -/
def LpmFormalLanguage : Language LpmSymbol :=
  { w | w ∈ LpmLanguage }

@[simp] theorem mem_LpmFormalLanguage
    (w : Word LpmSymbol) :
    w ∈ LpmFormalLanguage ↔
      w ∈ LpmLanguage := by
  rfl

/-- The left quotients by the prefixes a^n are pairwise distinct. -/
theorem lpm_leftQuotient_prefix_injective :
    Function.Injective
      (fun n : Nat =>
        LpmFormalLanguage.leftQuotient
          (List.replicate n a)) := by
  intro m n hmn
  let suffix : Word LpmSymbol :=
    e :: List.replicate m b
  have hm :
      suffix ∈
        LpmFormalLanguage.leftQuotient
          (List.replicate m a) := by
    change
      List.replicate m a ++
          (e :: List.replicate m b) ∈
        LpmLanguage
    simpa [lpmOneCenter, List.append_assoc] using
      (lpmOneCenter_e_mem_iff m m).2 rfl
  have hmn' :
      LpmFormalLanguage.leftQuotient
          (List.replicate m a) =
        LpmFormalLanguage.leftQuotient
          (List.replicate n a) := by
    simpa using hmn
  have hn :
      suffix ∈
        LpmFormalLanguage.leftQuotient
          (List.replicate n a) := by
    rw [← hmn']
    exact hm
  have hnFormal :
      List.replicate n a ++ suffix ∈
        LpmFormalLanguage := by
    exact hn
  have hnSet :
      List.replicate n a ++ suffix ∈
        LpmLanguage :=
    (mem_LpmFormalLanguage
      (List.replicate n a ++ suffix)).1
      hnFormal
  have hnmem :
      lpmOneCenter n e m ∈
        LpmLanguage := by
    simpa [suffix, lpmOneCenter,
      List.append_assoc] using hnSet
  exact
    ((lpmOneCenter_e_mem_iff n m).1 hnmem).symm

/-- Proposition 8.6, nonregularity component. -/
theorem lpm_not_regular :
    ¬ LpmFormalLanguage.IsRegular := by
  intro hreg
  have hfinite :
      (Set.range LpmFormalLanguage.leftQuotient).Finite :=
    (Language.isRegular_iff_finite_range_leftQuotient).1
      hreg
  have hinfinite :
      (Set.range
        (fun n : Nat =>
          LpmFormalLanguage.leftQuotient
            (List.replicate n a))).Infinite :=
    Set.infinite_range_of_injective
      lpm_leftQuotient_prefix_injective
  have hsubset :
      Set.range
          (fun n : Nat =>
            LpmFormalLanguage.leftQuotient
              (List.replicate n a))
        ⊆
      Set.range LpmFormalLanguage.leftQuotient := by
    rintro q ⟨n, rfl⟩
    exact ⟨List.replicate n a, rfl⟩
  exact hinfinite (hfinite.subset hsubset)

end TCS1
end LeanCfgProject
