import LeanCfgProject.TCS1.LinearSeparatorDistribution

/-!
# TCS #1 v77: pure-power context formulas for L_{±,e}

For center-containing factors, Section 8.1 reduces every admissible context
to a pair (a^m,b^n).  This module records the exact arithmetic membership
conditions for such contexts.  The separate context-shape lemma will justify
that no other contexts occur.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

theorem lpm_power_context_c_mem_iff
    (m n i j : Nat) :
    List.replicate m a ++
        lpmOneCenter i c j ++
        List.replicate n b ∈ LpmLanguage ↔
      m + i = j + n ∧ (m + i) % 2 = 0 := by
  rw [lpm_power_context_word]
  exact lpmOneCenter_c_mem_iff (m + i) (j + n)

theorem lpm_power_context_d_mem_iff
    (m n i j : Nat) :
    List.replicate m a ++
        lpmOneCenter i d j ++
        List.replicate n b ∈ LpmLanguage ↔
      m + i = j + n ∧ (m + i) % 2 = 1 := by
  rw [lpm_power_context_word]
  exact lpmOneCenter_d_mem_iff (m + i) (j + n)

theorem lpm_power_context_e_mem_iff
    (m n i j : Nat) :
    List.replicate m a ++
        lpmOneCenter i e j ++
        List.replicate n b ∈ LpmLanguage ↔
      m + i = j + n := by
  rw [lpm_power_context_word]
  exact lpmOneCenter_e_mem_iff (m + i) (j + n)

/-- Balance equality is exactly what is needed to transfer e-branch pure contexts. -/
theorem lpm_e_power_context_transfer
    {i j i' j' m n : Nat}
    (hbal : i + j' = i' + j) :
    (List.replicate m a ++
          lpmOneCenter i e j ++
          List.replicate n b ∈ LpmLanguage ↔
      List.replicate m a ++
          lpmOneCenter i' e j' ++
          List.replicate n b ∈ LpmLanguage) := by
  rw [lpm_power_context_e_mem_iff, lpm_power_context_e_mem_iff]
  omega


/--
The c/d branch of the Section 8.1 distribution argument, restricted to the
pure-power contexts that the context-shape lemma will later supply.

A shared pure context fixes both the balance offset and the parity phase, so
membership in any second pure context transfers from one factor to the other.
-/
theorem lpm_cd_power_context_fourth
    {z z' : LpmSymbol}
    (hz : z = c ∨ z = d)
    (hz' : z' = c ∨ z' = d)
    {r s m n i j i' j' : Nat}
    (hsharedX :
      List.replicate r a ++
          lpmOneCenter i z j ++
          List.replicate s b ∈ LpmLanguage)
    (hsharedY :
      List.replicate r a ++
          lpmOneCenter i' z' j' ++
          List.replicate s b ∈ LpmLanguage)
    (hctxX :
      List.replicate m a ++
          lpmOneCenter i z j ++
          List.replicate n b ∈ LpmLanguage) :
    List.replicate m a ++
        lpmOneCenter i' z' j' ++
        List.replicate n b ∈ LpmLanguage := by
  rcases hz with rfl | rfl <;>
    rcases hz' with rfl | rfl
  · rw [lpm_power_context_c_mem_iff] at hsharedX hsharedY hctxX ⊢
    omega
  · rw [lpm_power_context_c_mem_iff] at hsharedX hctxX
    rw [lpm_power_context_d_mem_iff] at hsharedY ⊢
    omega
  · rw [lpm_power_context_d_mem_iff] at hsharedX hctxX
    rw [lpm_power_context_c_mem_iff] at hsharedY ⊢
    omega
  · rw [lpm_power_context_d_mem_iff] at hsharedX hsharedY hctxX ⊢
    omega

/--
The e branch of the same argument: a shared pure context fixes the balance
offset, and that alone determines every other pure-power context.
-/
theorem lpm_e_power_context_fourth
    {r s m n i j i' j' : Nat}
    (hsharedX :
      List.replicate r a ++
          lpmOneCenter i e j ++
          List.replicate s b ∈ LpmLanguage)
    (hsharedY :
      List.replicate r a ++
          lpmOneCenter i' e j' ++
          List.replicate s b ∈ LpmLanguage)
    (hctxX :
      List.replicate m a ++
          lpmOneCenter i e j ++
          List.replicate n b ∈ LpmLanguage) :
    List.replicate m a ++
        lpmOneCenter i' e j' ++
        List.replicate n b ∈ LpmLanguage := by
  rw [lpm_power_context_e_mem_iff] at hsharedX hsharedY hctxX ⊢
  omega


end TCS1
end LeanCfgProject
