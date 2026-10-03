import LeanCfgProject.TCS1.LinearSeparatorBalance
import LeanCfgProject.TCS1.ClarkEyraudSpecialCase
import LeanCfgProject.TCS1.ZeroWindowEndpoint

/-!
# TCS #1 v88: endpoint-complete center-marker base

The v88 manuscript changes the unnumbered Section 10.1 comparison witness from
`{a^n c b^n : n > 0}` to the endpoint-complete language

  P = {a^n c b^n : n >= 0}.

This module verifies the new direct claim used in that paragraph: `P` is
Clark--Eyraud substitutable under the manuscript's nonempty-factor convention.

The proof follows the manuscript's two cases.  A factor containing the unique
center symbol has shape `a^i c b^j`, and its contexts are exactly pure
`a`-prefix / `b`-suffix pairs satisfying one balance equation.  A nonempty
factor avoiding the center is a pure positive `a`-power or `b`-power; shared
context then forces literal equality by the balance invariant.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- The endpoint-complete center-marker language P = {a^n c b^n : n >= 0}. -/
def CenterMarkerLanguage : Set (Word LpmSymbol) :=
  { w | ∃ n : Nat, w = lpmCore n c }

theorem centerMarker_core_mem (n : Nat) :
    lpmCore n c ∈ CenterMarkerLanguage := by
  exact ⟨n, rfl⟩

/-- Exact membership for a one-center factor. -/
theorem centerMarker_oneCenter_mem_iff
    (i j : Nat) :
    lpmOneCenter i c j ∈ CenterMarkerLanguage ↔ i = j := by
  constructor
  · rintro ⟨n, hword⟩
    have ha := congrArg (List.count a) hword
    have hb := congrArg (List.count b) hword
    have hin : i = n := by
      simpa [lpmOneCenter, lpmCore, List.count_replicate] using ha
    have hjn : j = n := by
      simpa [lpmOneCenter, lpmCore, List.count_replicate] using hb
    exact hin.trans hjn.symm
  · intro hij
    subst j
    exact ⟨i, rfl⟩

/-- Pure-power outer contexts are characterized by one balance equation. -/
theorem centerMarker_power_context_mem_iff
    (m n i j : Nat) :
    List.replicate m a ++
        lpmOneCenter i c j ++
        List.replicate n b ∈ CenterMarkerLanguage ↔
      m + i = j + n := by
  rw [lpm_power_context_word]
  exact centerMarker_oneCenter_mem_iff (m + i) (j + n)

/-- Every word of P has zero a/b balance. -/
theorem centerMarkerBalance_mem_zero
    {w : Word LpmSymbol}
    (hw : w ∈ CenterMarkerLanguage) :
    lpmBalance w = 0 := by
  rcases hw with ⟨n, rfl⟩
  simp [lpmCore, lpmBalance, List.count_replicate, List.count_append]

/-- A shared P-context forces equal factor balance. -/
theorem centerMarkerBalance_eq_of_sharedContext
    {x y : Word LpmSymbol}
    (hshared : HaveSharedContext CenterMarkerLanguage x y) :
    lpmBalance x = lpmBalance y := by
  rcases hshared with ⟨u, v, hxL, hyL⟩
  have hx0 := centerMarkerBalance_mem_zero hxL
  have hy0 := centerMarkerBalance_mem_zero hyL
  simp only [lpmBalance_append] at hx0 hy0
  omega

/-- Shared occurrence in P forces the two factors to contain equally many c's. -/
theorem centerMarker_count_c_eq_of_sharedContext
    {x y : Word LpmSymbol}
    (hshared : HaveSharedContext CenterMarkerLanguage x y) :
    x.count c = y.count c := by
  rcases hshared with ⟨u, v, hxL, hyL⟩
  rcases hxL with ⟨n, hxword⟩
  rcases hyL with ⟨m, hyword⟩
  have hxc := congrArg (List.count c) hxword
  have hyc := congrArg (List.count c) hyword
  simp [lpmCore, List.count_append, List.count_replicate] at hxc hyc
  omega

/--
If a one-center factor occurs in a P-word, the surrounding context is a pure
a-prefix and pure b-suffix.
-/
theorem centerMarker_context_shape
    {u v : Word LpmSymbol}
    {i j : Nat}
    (hmem :
      u ++ lpmOneCenter i c j ++ v ∈ CenterMarkerLanguage) :
    ∃ m n : Nat,
      u = List.replicate m a ∧
      v = List.replicate n b := by
  rcases hmem with ⟨N, hword⟩
  have hcanon :
      u ++
          (List.replicate i a ++ [c] ++ List.replicate j b) ++
          v =
        List.replicate N a ++ [c] ++ List.replicate N b := by
    simpa [lpmOneCenter, lpmCore, List.append_assoc] using hword
  obtain ⟨m, hum⟩ :=
    prefix_context_is_power
      a b c c (by decide)
      (i := i) (j := j) (p := N) (q := N)
      (u := u) (v := v)
      hcanon
  obtain ⟨n, hvn⟩ :=
    suffix_context_is_power
      a b c c (by decide)
      (i := i) (j := j) (p := N) (q := N)
      (u := u) (v := v)
      hcanon
  exact ⟨m, n, hum, hvn⟩

/--
A factor of a P-word containing c has the canonical shape a^i c b^j, with
pure-power context on both sides.
-/
theorem centerMarker_factor_shape_of_center_mem
    {u x v : Word LpmSymbol}
    (hcx : c ∈ x)
    (hmem : u ++ x ++ v ∈ CenterMarkerLanguage) :
    ∃ m i j n : Nat,
      u = List.replicate m a ∧
      x = lpmOneCenter i c j ∧
      v = List.replicate n b := by
  obtain ⟨xL, xR, hxsplit⟩ :=
    exists_split_around_mem hcx
  subst x
  rcases hmem with ⟨N, hword⟩
  have hwhole :
      (u ++ xL) ++
          ([] ++ [c] ++ []) ++
          (xR ++ v) =
        List.replicate N a ++ [c] ++
          List.replicate N b := by
    simpa [lpmCore, List.append_assoc] using hword

  obtain ⟨M, hprefix⟩ :=
    prefix_context_is_power
      a b c c (by decide)
      (i := 0) (j := 0) (p := N) (q := N)
      (u := u ++ xL) (v := xR ++ v)
      hwhole
  obtain ⟨K, hsuffix⟩ :=
    suffix_context_is_power
      a b c c (by decide)
      (i := 0) (j := 0) (p := N) (q := N)
      (u := u ++ xL) (v := xR ++ v)
      hwhole

  have hprefSub :
      u ++ xL ⊆ [a] := by
    rw [hprefix]
    exact List.replicate_subset_singleton M a
  have huSub : u ⊆ [a] := by
    intro t ht
    exact hprefSub (by simp [ht])
  have hxLSub : xL ⊆ [a] := by
    intro t ht
    exact hprefSub (by simp [ht])
  obtain ⟨m, hum⟩ :=
    List.subset_singleton_iff.mp huSub
  obtain ⟨i, hxLi⟩ :=
    List.subset_singleton_iff.mp hxLSub

  have hsufSub :
      xR ++ v ⊆ [b] := by
    rw [hsuffix]
    exact List.replicate_subset_singleton K b
  have hxRSub : xR ⊆ [b] := by
    intro t ht
    exact hsufSub (by simp [ht])
  have hvSub : v ⊆ [b] := by
    intro t ht
    exact hsufSub (by simp [ht])
  obtain ⟨j, hxRj⟩ :=
    List.subset_singleton_iff.mp hxRSub
  obtain ⟨n, hvn⟩ :=
    List.subset_singleton_iff.mp hvSub

  refine ⟨m, i, j, n, hum, ?_, hvn⟩
  simp [lpmOneCenter, hxLi, hxRj]

/--
A nonempty factor of a P-word that avoids c is a positive pure a-power or
positive pure b-power.
-/
theorem centerMarker_boundary_factor_shape
    {u x v : Word LpmSymbol}
    (hxne : x ≠ [])
    (hcx : c ∉ x)
    (hmem : u ++ x ++ v ∈ CenterMarkerLanguage) :
    (∃ n : Nat, 0 < n ∧ x = List.replicate n a) ∨
    (∃ n : Nat, 0 < n ∧ x = List.replicate n b) := by
  rcases hmem with ⟨N, hword⟩
  have hcwhole :
      c ∈ u ++ x ++ v := by
    rw [hword]
    simp [lpmCore]
  have hcases :
      (c ∈ u ∨ c ∈ x) ∨ c ∈ v := by
    simpa only [List.mem_append] using hcwhole

  rcases hcases with (hcu | hcx') | hcv
  · obtain ⟨uL, uR, husplit⟩ :=
      exists_split_around_mem hcu
    have hmarker :
        uL ++
            ([] ++ [c] ++ []) ++
            (uR ++ x ++ v) =
          List.replicate N a ++ [c] ++
            List.replicate N b := by
      rw [husplit] at hword
      simpa [lpmCore, List.append_assoc] using hword
    obtain ⟨K, hsuffix⟩ :=
      suffix_context_is_power
        a b c c (by decide)
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
      have : x = [] := by simpa using hxn
      exact hxne this
    exact Or.inr ⟨n, Nat.pos_of_ne_zero hn0, hxn⟩
  · exact False.elim (hcx hcx')
  · obtain ⟨vL, vR, hvsplit⟩ :=
      exists_split_around_mem hcv
    have hmarker :
        (u ++ x ++ vL) ++
            ([] ++ [c] ++ []) ++
            vR =
          List.replicate N a ++ [c] ++
            List.replicate N b := by
      rw [hvsplit] at hword
      simpa [lpmCore, List.append_assoc] using hword
    obtain ⟨K, hprefix⟩ :=
      prefix_context_is_power
        a b c c (by decide)
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
      have : x = [] := by simpa using hxn
      exact hxne this
    exact Or.inl ⟨n, Nat.pos_of_ne_zero hn0, hxn⟩

/-- Boundary-only factors sharing a P-context are literally equal. -/
theorem centerMarker_boundary_factors_eq
    {x y : Word LpmSymbol}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hcx : c ∉ x)
    (hcy : c ∉ y)
    (hshared : HaveSharedContext CenterMarkerLanguage x y) :
    x = y := by
  rcases hshared with ⟨u, v, hxL, hyL⟩
  have hbal :
      lpmBalance x = lpmBalance y :=
    centerMarkerBalance_eq_of_sharedContext
      ⟨u, v, hxL, hyL⟩
  rcases centerMarker_boundary_factor_shape hxne hcx hxL with
      ⟨m, hmpos, hxa⟩ | ⟨m, hmpos, hxbpow⟩ <;>
    rcases centerMarker_boundary_factor_shape hyne hcy hyL with
      ⟨n, hnpos, hya⟩ | ⟨n, hnpos, hybpow⟩
  · rw [hxa, hya] at hbal ⊢
    simp at hbal
    have hmn : m = n := by omega
    subst n
    rfl
  · rw [hxa, hybpow] at hbal
    simp at hbal
    omega
  · rw [hxbpow, hya] at hbal
    simp at hbal
    omega
  · rw [hxbpow, hybpow] at hbal ⊢
    simp at hbal
    have hmn : m = n := by omega
    subst n
    rfl

/-- Center-containing factors sharing a P-context have equal distributions. -/
theorem centerMarker_center_factors_distribution_eq
    {x y : Word LpmSymbol}
    (hcx : c ∈ x)
    (hcy : c ∈ y)
    (hshared : HaveSharedContext CenterMarkerLanguage x y) :
    Distribution CenterMarkerLanguage x =
      Distribution CenterMarkerLanguage y := by
  rcases hshared with ⟨u, v, hxL, hyL⟩
  obtain ⟨m, i, j, n, hum, hxshape, hvn⟩ :=
    centerMarker_factor_shape_of_center_mem hcx hxL
  obtain ⟨_m', i', j', _n', _hum', hyshape, _hvn'⟩ :=
    centerMarker_factor_shape_of_center_mem hcy hyL

  have hsharedX :
      List.replicate m a ++
          lpmOneCenter i c j ++
          List.replicate n b ∈ CenterMarkerLanguage := by
    simpa [hum, hxshape, hvn, List.append_assoc] using hxL
  have hsharedY :
      List.replicate m a ++
          lpmOneCenter i' c j' ++
          List.replicate n b ∈ CenterMarkerLanguage := by
    simpa [hum, hyshape, hvn, List.append_assoc] using hyL
  have heqX :=
    (centerMarker_power_context_mem_iff m n i j).1 hsharedX
  have heqY :=
    (centerMarker_power_context_mem_iff m n i' j').1 hsharedY
  have hoffset : i + j' = i' + j := by
    omega

  apply Set.ext
  rintro ⟨r, s⟩
  change
    (r ++ x ++ s ∈ CenterMarkerLanguage) ↔
      (r ++ y ++ s ∈ CenterMarkerLanguage)
  constructor
  · intro hctxX
    have hctxX' :
        r ++ lpmOneCenter i c j ++ s ∈ CenterMarkerLanguage := by
      simpa [hxshape] using hctxX
    obtain ⟨p, q, hrp, hsq⟩ :=
      centerMarker_context_shape hctxX'
    have hpureX :
        List.replicate p a ++
            lpmOneCenter i c j ++
            List.replicate q b ∈ CenterMarkerLanguage := by
      simpa [hrp, hsq, List.append_assoc] using hctxX'
    have heq :=
      (centerMarker_power_context_mem_iff p q i j).1 hpureX
    have hpureY :
        List.replicate p a ++
            lpmOneCenter i' c j' ++
            List.replicate q b ∈ CenterMarkerLanguage := by
      apply (centerMarker_power_context_mem_iff p q i' j').2
      omega
    simpa [hrp, hsq, hyshape, List.append_assoc] using hpureY
  · intro hctxY
    have hctxY' :
        r ++ lpmOneCenter i' c j' ++ s ∈ CenterMarkerLanguage := by
      simpa [hyshape] using hctxY
    obtain ⟨p, q, hrp, hsq⟩ :=
      centerMarker_context_shape hctxY'
    have hpureY :
        List.replicate p a ++
            lpmOneCenter i' c j' ++
            List.replicate q b ∈ CenterMarkerLanguage := by
      simpa [hrp, hsq, List.append_assoc] using hctxY'
    have heq :=
      (centerMarker_power_context_mem_iff p q i' j').1 hpureY
    have hpureX :
        List.replicate p a ++
            lpmOneCenter i c j ++
            List.replicate q b ∈ CenterMarkerLanguage := by
      apply (centerMarker_power_context_mem_iff p q i j).2
      omega
    simpa [hrp, hsq, hxshape, List.append_assoc] using hpureX

/--
The v88 Section 10.1 base claim: the endpoint-complete center-marker language
P is Clark--Eyraud substitutable.
-/
theorem centerMarker_clarkEyraud :
    ClarkEyraudSubstitutableOn CenterMarkerLanguage := by
  intro x y hxne hyne hshared
  have hcount :
      x.count c = y.count c :=
    centerMarker_count_c_eq_of_sharedContext hshared
  by_cases hcx : c ∈ x
  · have hcy : c ∈ y := by
      have hxpos : 0 < x.count c :=
        List.count_pos.mpr hcx
      have hypos : 0 < y.count c := by
        rw [← hcount]
        exact hxpos
      exact List.count_pos.mp hypos
    exact
      centerMarker_center_factors_distribution_eq
        hcx hcy hshared
  · have hcy : c ∉ y := by
      intro hcy
      have hypos : 0 < y.count c :=
        List.count_pos.mpr hcy
      have hxpos : 0 < x.count c := by
        rw [hcount]
        exact hypos
      exact hcx (List.count_pos.mp hxpos)
    have hxy :=
      centerMarker_boundary_factors_eq
        hxne hyne hcx hcy hshared
    subst y
    rfl

/-- Consequently P belongs to the concrete (0,0)-fixed-window class. -/
theorem centerMarker_zeroWindow :
    FixedWindowSubstitutable 0 0 CenterMarkerLanguage := by
  rw [zeroWindowSubstitutable_iff_nonemptyFactorSubstitutable]
  exact centerMarker_clarkEyraud

end TCS1
end LeanCfgProject
