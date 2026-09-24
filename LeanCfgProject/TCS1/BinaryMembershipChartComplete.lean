import LeanCfgProject.TCS1.BinaryMembershipChartSound

/-!
# TCS #1 v79: completeness helpers for the executable CYK chart

This module develops the converse direction to chart soundness.  The first
layer proves the exact span arithmetic, terminal-seed completeness, arbitrary
round monotonicity, and one-step binary insertion theorem needed by the final
CYK completeness induction.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryMembershipChartComplete

variable {N : Type u}
variable {α : Type v}

/-- A CYK slice never exceeds the numeric boundary width. -/
theorem cykSlice_length_le_span
    (w : Word α)
    (i j : Fin (w.length + 1)) :
    (cykSlice w i j).length ≤ j.1 - i.1 := by
  unfold cykSlice
  simp only [List.length_take]
  omega

/-- On an ordered interval, a CYK slice has exactly the boundary width. -/
theorem cykSlice_length_eq_span
    (w : Word α)
    (i j : Fin (w.length + 1))
    (hij : i.1 ≤ j.1) :
    (cykSlice w i j).length = j.1 - i.1 := by
  unfold cykSlice
  simp only [List.length_take, List.length_drop]
  have hj : j.1 ≤ w.length := by
    omega
  omega

/-- The executable terminal seed contains every enabled terminal position. -/
theorem cykTerminalSeed_complete
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (w : Word α)
    (A : N)
    (i : Fin w.length)
    (hterm : terminalRule A (w.get i)) :
    (A,
      (cykLeftBoundary i,
        cykRightBoundary i))
      ∈ cykTerminalSeed terminalRule w := by
  unfold cykTerminalSeed
  apply Finset.mem_image.2
  refine ⟨(A, i), ?_, rfl⟩
  apply Finset.mem_filter.2
  exact ⟨Finset.mem_univ _, hterm⟩

/-- Executable chart iterations are monotone in the round counter. -/
theorem cykChartIterate_mono
    [Fintype N]
    [DecidableEq N]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    {n : Nat}
    (seed : CYKChart N n)
    {r s : Nat}
    (hrs : r ≤ s) :
    cykChartIterate binaryRule seed r ⊆
      cykChartIterate binaryRule seed s := by
  induction s, hrs using Nat.le_induction with
  | base =>
      intro e he
      exact he
  | succ s hrs ih =>
      intro e he
      exact
        cykChartIterate_mono_succ
          binaryRule seed s (ih he)

/--
If both child spans are present in the old chart and a binary rule joins them
at a strict split point, the parent span is present after one executable step.
-/
theorem cykChartStep_complete_binary
    [Fintype N]
    [DecidableEq N]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    {n : Nat}
    (old : CYKChart N n)
    (A B C : N)
    (i k j : Fin (n + 1))
    (hik : i.1 < k.1)
    (hkj : k.1 < j.1)
    (hbin : binaryRule A B C)
    (hleft : (B, (i, k)) ∈ old)
    (hright : (C, (k, j)) ∈ old) :
    (A, (i, j)) ∈
      cykChartStep binaryRule old := by
  apply Finset.mem_union_right
  apply
    (mem_cykProduced_iff
      binaryRule old (A, (i, j))).2
  let c : CYKBinaryCandidate N n :=
    ((A, B, C), (i, k, j))
  refine ⟨c, ?_, rfl⟩
  exact ⟨hik, hkj, hbin, hleft, hright⟩

end BinaryMembershipChartComplete

end TCS1
end LeanCfgProject
