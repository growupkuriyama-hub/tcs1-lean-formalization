import LeanCfgProject.TCS1.LinearSeparatorContextShape

/-!
# TCS #1 v78: boundary-only factors of L_{±,e}

This module formalizes the other structural case needed by the fixed-h proof:
a nonempty factor of a separator word that contains no center symbol must lie
entirely on one side of the unique center.  Hence it is a positive pure
a-power or a positive pure b-power.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

theorem accepted_center_symbol
    {n : Nat} {z : LpmSymbol}
    (hacc : LpmAccepted n z) :
    LpmCenterSymbol z := by
  cases z <;>
    simp [LpmAccepted, LpmCenterSymbol] at hacc ⊢

theorem center_not_boundary
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z) :
    ¬ LpmBoundaryLetter z := by
  rcases hz with rfl | rfl | rfl <;>
    simp [LpmBoundaryLetter]

/--
A nonempty factor occurring in L_{±,e} and typed by the identity is either
a positive a-power or a positive b-power.
-/
theorem lpm_boundary_factor_shape
    {u x v : Word LpmSymbol}
    (hxne : x ≠ [])
    (hboundary :
      ∀ t ∈ x, LpmBoundaryLetter t)
    (hmem : u ++ x ++ v ∈ LpmLanguage) :
    (∃ n : Nat, 0 < n ∧ x = List.replicate n a) ∨
    (∃ n : Nat, 0 < n ∧ x = List.replicate n b) := by
  rcases hmem with ⟨N, z', hword, hacc⟩
  have hzcenter : LpmCenterSymbol z' :=
    accepted_center_symbol hacc
  have hzwhole :
      z' ∈ u ++ x ++ v := by
    rw [hword]
    simp [lpmCore]
  have hzcases :
      (z' ∈ u ∨ z' ∈ x) ∨ z' ∈ v := by
    simpa only [List.mem_append] using hzwhole
  have hznotx : z' ∉ x := by
    intro hzx
    exact
      center_not_boundary hzcenter
        (hboundary z' hzx)

  rcases hzcases with (hzu | hzx) | hzv
  · obtain ⟨uL, uR, husplit⟩ :=
      exists_split_around_mem hzu
    have hmarker :
        uL ++
            ([] ++ [z'] ++ []) ++
            (uR ++ x ++ v) =
          List.replicate N a ++ [z'] ++
            List.replicate N b := by
      rw [husplit] at hword
      simpa [lpmCore, List.append_assoc] using hword
    obtain ⟨K, hsuffix⟩ :=
      suffix_context_is_power
        a b z' z' (center_ne_a hzcenter)
        (i := 0) (j := 0) (p := N) (q := N)
        (u := uL) (v := uR ++ x ++ v)
        hmarker
    have hsufSub :
        uR ++ x ++ v ⊆ [b] := by
      rw [hsuffix]
      exact List.replicate_subset_singleton K b
    have hxSub : x ⊆ [b] := by
      intro t ht
      exact hsufSub (by simp [ht])
    obtain ⟨n, hxn⟩ :=
      List.subset_singleton_iff.mp hxSub
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      have : x = [] := by
        simpa using hxn
      exact hxne this
    exact Or.inr ⟨n, Nat.pos_of_ne_zero hn0, hxn⟩

  · exact False.elim (hznotx hzx)

  · obtain ⟨vL, vR, hvsplit⟩ :=
      exists_split_around_mem hzv
    have hmarker :
        (u ++ x ++ vL) ++
            ([] ++ [z'] ++ []) ++
            vR =
          List.replicate N a ++ [z'] ++
            List.replicate N b := by
      rw [hvsplit] at hword
      simpa [lpmCore, List.append_assoc] using hword
    obtain ⟨K, hprefix⟩ :=
      prefix_context_is_power
        a b z' z' (center_ne_b hzcenter)
        (i := 0) (j := 0) (p := N) (q := N)
        (u := u ++ x ++ vL) (v := vR)
        hmarker
    have hprefSub :
        u ++ x ++ vL ⊆ [a] := by
      rw [hprefix]
      exact List.replicate_subset_singleton K a
    have hxSub : x ⊆ [a] := by
      intro t ht
      exact hprefSub (by simp [ht])
    obtain ⟨n, hxn⟩ :=
      List.subset_singleton_iff.mp hxSub
    have hn0 : n ≠ 0 := by
      intro hn
      subst n
      have : x = [] := by
        simpa using hxn
      exact hxne this
    exact Or.inl ⟨n, Nat.pos_of_ne_zero hn0, hxn⟩

end TCS1
end LeanCfgProject
