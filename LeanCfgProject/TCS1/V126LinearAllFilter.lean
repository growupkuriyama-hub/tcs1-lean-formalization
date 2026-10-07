import LeanCfgProject.TCS1.LinearSeparatorFixedH
import Mathlib.Tactic

/-!
# TCS #1 v126: the regular-filter presentation of the linear separator

The current manuscript introduces

  L_all = { a^n z b^n : n >= 0, z in {c,d,e} }

and states that L_all is Clark--Eyraud substitutable.  It then writes the
separator L_{±,e} as L_all intersected with a regular parity filter.

This file formalizes the paper-owned semantic statements.  Regularity of the
filter is isolated for a separate finite-automaton module.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- The center-uniform balanced language L_all from the manuscript. -/
def LpmAllLanguage : Set (Word LpmSymbol) :=
  {w | ∃ n z,
    w = lpmCore n z ∧ LpmCenterSymbol z}

/-- Number of center symbols c,d,e in a word. -/
def lpmCenterCount (w : Word LpmSymbol) : Nat :=
  w.count c + w.count d + w.count e

@[simp] theorem lpmCenterCount_nil :
    lpmCenterCount ([] : Word LpmSymbol) = 0 := by
  simp [lpmCenterCount]

@[simp] theorem lpmCenterCount_append
    (u v : Word LpmSymbol) :
    lpmCenterCount (u ++ v) =
      lpmCenterCount u + lpmCenterCount v := by
  simp [lpmCenterCount, List.count_append]
  omega

/-- Every L_all word has exactly one center. -/
theorem lpmAll_centerCount_one
    {w : Word LpmSymbol}
    (hw : w ∈ LpmAllLanguage) :
    lpmCenterCount w = 1 := by
  rcases hw with ⟨n, z, rfl, hz⟩
  rcases hz with rfl | rfl | rfl <;>
    simp [lpmCore, lpmCenterCount, List.count_append,
      List.count_replicate]

/-- Center count zero is exactly the boundary-only condition. -/
theorem lpmCenterCount_eq_zero_iff_boundary_only
    (w : Word LpmSymbol) :
    lpmCenterCount w = 0 ↔
      ∀ z ∈ w, LpmBoundaryLetter z := by
  constructor
  · intro h z hz
    cases z with
    | a => exact Or.inl rfl
    | b => exact Or.inr rfl
    | c =>
        have hc : 0 < w.count c :=
          (List.count_pos_iff).2 hz
        unfold lpmCenterCount at h
        omega
    | d =>
        have hd : 0 < w.count d :=
          (List.count_pos_iff).2 hz
        unfold lpmCenterCount at h
        omega
    | e =>
        have he : 0 < w.count e :=
          (List.count_pos_iff).2 hz
        unfold lpmCenterCount at h
        omega
  · intro h
    have hc : w.count c = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hcpos
      have hc : c ∈ w := (List.count_pos_iff).1 hcpos
      rcases h c hc with hcEq | hcEq <;> cases hcEq
    have hd : w.count d = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hdpos
      have hd : d ∈ w := (List.count_pos_iff).1 hdpos
      rcases h d hd with hdEq | hdEq <;> cases hdEq
    have he : w.count e = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hepos
      have he : e ∈ w := (List.count_pos_iff).1 hepos
      rcases h e he with heEq | heEq <;> cases heEq
    simp [lpmCenterCount, hc, hd, he]

/-- Shared occurrence in L_all forces equal center counts. -/
theorem lpmAll_centerCount_eq_of_sharedContext
    {x y : Word LpmSymbol}
    (hshared : HaveSharedContext LpmAllLanguage x y) :
    lpmCenterCount x = lpmCenterCount y := by
  rcases hshared with ⟨u, v, hx, hy⟩
  have hx1 := lpmAll_centerCount_one hx
  have hy1 := lpmAll_centerCount_one hy
  simp only [lpmCenterCount_append] at hx1 hy1
  omega

/-- Every L_all word has zero a/b balance. -/
theorem lpmAll_balance_zero
    {w : Word LpmSymbol}
    (hw : w ∈ LpmAllLanguage) :
    lpmBalance w = 0 := by
  rcases hw with ⟨n, z, rfl, hz⟩
  rcases hz with rfl | rfl | rfl <;>
    simp [lpmCore, lpmBalance, List.count_append,
      List.count_replicate]

/-- Shared occurrence in L_all forces equal factor balance. -/
theorem lpmAll_balance_eq_of_sharedContext
    {x y : Word LpmSymbol}
    (hshared : HaveSharedContext LpmAllLanguage x y) :
    lpmBalance x = lpmBalance y := by
  rcases hshared with ⟨u, v, hx, hy⟩
  have hx0 := lpmAll_balance_zero hx
  have hy0 := lpmAll_balance_zero hy
  simp only [lpmBalance_append] at hx0 hy0
  omega

/-- Exact L_all membership of a possibly unbalanced one-center word. -/
theorem lpmAll_oneCenter_mem_iff
    (i j : Nat) (z : LpmSymbol) :
    lpmOneCenter i z j ∈ LpmAllLanguage ↔
      i = j ∧ LpmCenterSymbol z := by
  constructor
  · rintro ⟨n, z', hword, hz'⟩
    have hzmem :
        z' ∈ lpmOneCenter i z j := by
      rw [hword]
      simp [lpmCore]
    have hzz : z = z' := by
      rcases hz' with rfl | rfl | rfl <;>
        simp [lpmOneCenter, List.mem_replicate] at hzmem <;>
        exact hzmem.symm
    subst z'
    have hzcenter : LpmCenterSymbol z := hz'
    have ha := congrArg (List.count a) hword
    have hb := congrArg (List.count b) hword
    have hi : i = n := by
      rcases hzcenter with rfl | rfl | rfl <;>
        simpa [lpmOneCenter, lpmCore, List.count_append,
          List.count_replicate] using ha
    have hj : j = n := by
      rcases hzcenter with rfl | rfl | rfl <;>
        simpa [lpmOneCenter, lpmCore, List.count_append,
          List.count_replicate] using hb
    exact ⟨hi.trans hj.symm, hzcenter⟩
  · rintro ⟨rfl, hz⟩
    exact ⟨i, z, rfl, hz⟩

/-- A center-containing factor of an L_all word has the canonical
a^i z b^j shape, and its outer context is a pure a-prefix / b-suffix. -/
theorem lpmAll_factor_shape_of_center_mem
    {u x v : Word LpmSymbol}
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z)
    (hzx : z ∈ x)
    (hmem : u ++ x ++ v ∈ LpmAllLanguage) :
    ∃ m i j n : Nat,
      u = List.replicate m a ∧
      x = lpmOneCenter i z j ∧
      v = List.replicate n b := by
  obtain ⟨xL, xR, hxsplit⟩ :=
    exists_split_around_mem hzx
  subst x
  rcases hmem with ⟨N, z', hword, hz'⟩
  have hwhole :
      (u ++ xL) ++
          ([] ++ [z] ++ []) ++
          (xR ++ v) =
        List.replicate N a ++ [z'] ++
          List.replicate N b := by
    simpa [lpmCore, List.append_assoc] using hword
  obtain ⟨M, hprefix⟩ :=
    prefix_context_is_power
      a b z z' (center_ne_b hz)
      (i := 0) (j := 0) (p := N) (q := N)
      (u := u ++ xL) (v := xR ++ v)
      hwhole
  obtain ⟨K, hsuffix⟩ :=
    suffix_context_is_power
      a b z z' (center_ne_a hz)
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

/-- A nonempty center-free factor of an L_all word is a positive pure a-power
or a positive pure b-power. -/
theorem lpmAll_boundary_factor_shape
    {u x v : Word LpmSymbol}
    (hxne : x ≠ [])
    (hboundary :
      ∀ t ∈ x, LpmBoundaryLetter t)
    (hmem : u ++ x ++ v ∈ LpmAllLanguage) :
    (∃ n : Nat, 0 < n ∧ x = List.replicate n a) ∨
    (∃ n : Nat, 0 < n ∧ x = List.replicate n b) := by
  rcases hmem with ⟨N, z', hword, hzcenter⟩
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
        uL ++ ([] ++ [z'] ++ []) ++
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
      have : x = [] := by simpa using hxn
      exact hxne this
    exact Or.inr ⟨n, Nat.pos_of_ne_zero hn0, hxn⟩
  · exact False.elim (hznotx hzx)
  · obtain ⟨vL, vR, hvsplit⟩ :=
      exists_split_around_mem hzv
    have hmarker :
        (u ++ x ++ vL) ++ ([] ++ [z'] ++ []) ++
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
      have : x = [] := by simpa using hxn
      exact hxne this
    exact Or.inl ⟨n, Nat.pos_of_ne_zero hn0, hxn⟩

/-- Boundary-only factors with a shared L_all context are literally equal. -/
theorem lpmAll_boundary_factors_eq
    {x y : Word LpmSymbol}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hxb : ∀ t ∈ x, LpmBoundaryLetter t)
    (hyb : ∀ t ∈ y, LpmBoundaryLetter t)
    (hshared : HaveSharedContext LpmAllLanguage x y) :
    x = y := by
  rcases hshared with ⟨u, v, hxL, hyL⟩
  have hbal :=
    lpmAll_balance_eq_of_sharedContext
      ⟨u, v, hxL, hyL⟩
  rcases lpmAll_boundary_factor_shape hxne hxb hxL with
      ⟨m, hmpos, hxa⟩ | ⟨m, hmpos, hxbpow⟩ <;>
    rcases lpmAll_boundary_factor_shape hyne hyb hyL with
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

/-- Distribution membership of one-center factors in L_all depends only on
the balance i-j, not on which center c,d,e is used. -/
theorem lpmAll_oneCenter_distribution_transfer
    {i j i' j' : Nat}
    {z z' : LpmSymbol}
    (hz : LpmCenterSymbol z)
    (hz' : LpmCenterSymbol z')
    (hbal :
      (i : Int) - (j : Int) =
        (i' : Int) - (j' : Int))
    {u v : Word LpmSymbol}
    (hctx :
      (u, v) ∈ Distribution LpmAllLanguage
        (lpmOneCenter i z j)) :
    (u, v) ∈ Distribution LpmAllLanguage
        (lpmOneCenter i' z' j') := by
  change
    u ++ lpmOneCenter i z j ++ v ∈
      LpmAllLanguage at hctx
  obtain ⟨m, _ii, _jj, n, hu, hxshape, hv⟩ :=
    lpmAll_factor_shape_of_center_mem hz
      (by simp [lpmOneCenter]) hctx
  have hii : _ii = i := by
    have h := congrArg (List.count a) hxshape
    rcases hz with rfl | rfl | rfl <;>
      simpa [lpmOneCenter, List.count_append,
        List.count_replicate] using h.symm
  have hjj : _jj = j := by
    have h := congrArg (List.count b) hxshape
    rcases hz with rfl | rfl | rfl <;>
      simpa [lpmOneCenter, List.count_append,
        List.count_replicate] using h.symm
  subst _ii
  subst _jj
  subst u
  subst v
  change
    (List.replicate m a ++
      lpmOneCenter i' z' j' ++
      List.replicate n b) ∈ LpmAllLanguage
  rw [lpm_power_context_word] at hctx ⊢
  have hmem :=
    (lpmAll_oneCenter_mem_iff
      (m + i) (j + n) z).1 hctx
  have hEq : m + i' = j' + n := by
    rcases hmem with ⟨hEq0, _⟩
    omega
  exact
    (lpmAll_oneCenter_mem_iff
      (m + i') (j' + n) z').2
      ⟨hEq, hz'⟩

/-- The manuscript's unnumbered claim: L_all is Clark--Eyraud substitutable
under the nonempty-factor convention. -/
theorem lpmAll_clarkEyraudSubstitutable :
    ClarkEyraudSubstitutable LpmAllLanguage := by
  intro x y hxne hyne hshared
  have hcount :
      lpmCenterCount x = lpmCenterCount y :=
    lpmAll_centerCount_eq_of_sharedContext hshared
  by_cases hx0 : lpmCenterCount x = 0
  · have hy0 : lpmCenterCount y = 0 := by
      rw [← hcount]
      exact hx0
    have hxb :=
      (lpmCenterCount_eq_zero_iff_boundary_only x).1 hx0
    have hyb :=
      (lpmCenterCount_eq_zero_iff_boundary_only y).1 hy0
    have hxy :=
      lpmAll_boundary_factors_eq
        hxne hyne hxb hyb hshared
    subst y
    rfl
  · have hxpos : 0 < lpmCenterCount x := Nat.pos_of_ne_zero hx0
    have hypos : 0 < lpmCenterCount y := by
      rw [← hcount]
      exact hxpos
    have hxcenter : ∃ z ∈ x, LpmCenterSymbol z := by
      unfold lpmCenterCount at hxpos
      by_cases hc : 0 < x.count c
      · exact ⟨c, (List.count_pos_iff).1 hc, Or.inl rfl⟩
      · by_cases hd : 0 < x.count d
        · exact ⟨d, (List.count_pos_iff).1 hd, Or.inr (Or.inl rfl)⟩
        · have he : 0 < x.count e := by omega
          exact ⟨e, (List.count_pos_iff).1 he, Or.inr (Or.inr rfl)⟩
    have hycenter : ∃ z ∈ y, LpmCenterSymbol z := by
      unfold lpmCenterCount at hypos
      by_cases hc : 0 < y.count c
      · exact ⟨c, (List.count_pos_iff).1 hc, Or.inl rfl⟩
      · by_cases hd : 0 < y.count d
        · exact ⟨d, (List.count_pos_iff).1 hd, Or.inr (Or.inl rfl)⟩
        · have he : 0 < y.count e := by omega
          exact ⟨e, (List.count_pos_iff).1 he, Or.inr (Or.inr rfl)⟩
    rcases hshared with ⟨u0, v0, hxL, hyL⟩
    rcases hxcenter with ⟨zx, hzxmem, hzxc⟩
    rcases hycenter with ⟨zy, hzymem, hzyc⟩
    obtain ⟨mx, i, j, nx, huX, hxshape, hvX⟩ :=
      lpmAll_factor_shape_of_center_mem hzxc hzxmem hxL
    obtain ⟨my, i', j', ny, huY, hyshape, hvY⟩ :=
      lpmAll_factor_shape_of_center_mem hzyc hzymem hyL
    have hbalxy :
        lpmBalance x = lpmBalance y :=
      lpmAll_balance_eq_of_sharedContext
        ⟨u0, v0, hxL, hyL⟩
    have hdiff :
        (i : Int) - (j : Int) =
          (i' : Int) - (j' : Int) := by
      rw [hxshape, hyshape] at hbalxy
      rcases hzxc with rfl | rfl | rfl <;>
        rcases hzyc with rfl | rfl | rfl <;>
        simpa [lpmBalance, lpmOneCenter,
          List.count_append, List.count_replicate] using hbalxy
    rw [hxshape, hyshape]
    apply Set.ext
    rintro ⟨u, v⟩
    constructor
    · exact
        lpmAll_oneCenter_distribution_transfer
          hzxc hzyc hdiff
    · exact
        lpmAll_oneCenter_distribution_transfer
          hzyc hzxc hdiff.symm

/-- Semantic form of the paper's regular filter
(aa)^* c (bb)^* ∪ a(aa)^* d b(bb)^* ∪ a^* e b^*. -/
def LpmParityFilter : Set (Word LpmSymbol) :=
  {w | ∃ i j : Nat,
    (w = lpmOneCenter i c j ∧ i % 2 = 0 ∧ j % 2 = 0) ∨
    (w = lpmOneCenter i d j ∧ i % 2 = 1 ∧ j % 2 = 1) ∨
    (w = lpmOneCenter i e j)}

/-- The paper's exact filtering identity
L_{±,e} = L_all ∩ Q. -/
theorem lpmLanguage_eq_all_inter_parityFilter :
    LpmLanguage =
      LpmAllLanguage ∩ LpmParityFilter := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨n, z, rfl, hacc⟩
    constructor
    · have hz : LpmCenterSymbol z := accepted_center_symbol hacc
      exact ⟨n, z, rfl, hz⟩
    · refine ⟨n, n, ?_⟩
      cases z with
      | a => simp [LpmAccepted] at hacc
      | b => simp [LpmAccepted] at hacc
      | c =>
          left
          exact ⟨rfl, hacc, hacc⟩
      | d =>
          right; left
          exact ⟨rfl, hacc, hacc⟩
      | e =>
          right; right
          rfl
  · rintro ⟨hall, hq⟩
    rcases hall with ⟨n, z, hw, hz⟩
    rcases hq with ⟨i, j, hc | hd | he⟩
    · rcases hc with ⟨hcword, hie, hje⟩
      have hEq :
          lpmCore n z = lpmOneCenter i c j := by
        rw [← hw]
        exact hcword
      have ha := congrArg (List.count a) hEq
      have hb := congrArg (List.count b) hEq
      have hcCount := congrArg (List.count c) hEq
      have hnI : n = i := by
        rcases hz with rfl | rfl | rfl <;>
          simp [lpmCore, lpmOneCenter, List.count_append,
            List.count_replicate] at ha hcCount ⊢ <;> omega
      have hzC : z = c := by
        rcases hz with rfl | rfl | rfl <;>
          simp [lpmCore, lpmOneCenter, List.count_append,
            List.count_replicate] at hcCount ⊢
      subst z
      subst i
      exact ⟨n, c, hw, hie⟩
    · rcases hd with ⟨hdword, hio, hjo⟩
      have hEq :
          lpmCore n z = lpmOneCenter i d j := by
        rw [← hw]
        exact hdword
      have ha := congrArg (List.count a) hEq
      have hdCount := congrArg (List.count d) hEq
      have hnI : n = i := by
        rcases hz with rfl | rfl | rfl <;>
          simp [lpmCore, lpmOneCenter, List.count_append,
            List.count_replicate] at ha hdCount ⊢ <;> omega
      have hzD : z = d := by
        rcases hz with rfl | rfl | rfl <;>
          simp [lpmCore, lpmOneCenter, List.count_append,
            List.count_replicate] at hdCount ⊢
      subst z
      subst i
      exact ⟨n, d, hw, hio⟩
    · have hEq :
          lpmCore n z = lpmOneCenter i e j := by
        rw [← hw]
        exact he
      have heCount := congrArg (List.count e) hEq
      have hzE : z = e := by
        rcases hz with rfl | rfl | rfl <;>
          simp [lpmCore, lpmOneCenter, List.count_append,
            List.count_replicate] at heCount ⊢
      subst z
      exact ⟨n, e, hw, trivial⟩

end TCS1
end LeanCfgProject
