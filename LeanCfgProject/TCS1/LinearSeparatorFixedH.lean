import LeanCfgProject.TCS1.LinearSeparatorBalance
import LeanCfgProject.TCS1.LinearSeparatorPowerContexts

/-!
# TCS #1 v78: fixed-h substitutability of L_{±,e}

This module packages the revised Section 8.1 positive separation argument.
The identity branch uses the balance kernel.  The kappa_cd and kappa_e
branches use the context-shape theorem plus the already verified pure-power
context transfer lemmas.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol LpmType

@[simp] theorem lpmTyping_oneCenter
    (i j : Nat) (z : LpmSymbol) :
    lpmTyping.h (lpmOneCenter i z j) =
      lpmLetterType z := by
  simp [lpmOneCenter, lpmTyping, lpmLetterType,
    List.map_append, List.prod_append]

theorem lpmLetterType_eq_cd_iff
    (z : LpmSymbol) :
    lpmLetterType z = cd ↔ z = c ∨ z = d := by
  cases z <;> simp [lpmLetterType]

theorem lpmLetterType_eq_ee_iff
    (z : LpmSymbol) :
    lpmLetterType z = ee ↔ z = e := by
  cases z <;> simp [lpmLetterType]

/-- A non-identity typed factor must contain one of the three center symbols. -/
theorem exists_center_mem_of_typing_ne_one
    (w : Word LpmSymbol)
    (hne : lpmTyping.h w ≠ 1) :
    ∃ z : LpmSymbol,
      z ∈ w ∧ LpmCenterSymbol z := by
  by_contra h
  push_neg at h
  have hall :
      ∀ z ∈ w, LpmBoundaryLetter z := by
    intro z hz
    have hncenter := h z hz
    cases z <;>
      simp [LpmCenterSymbol, LpmBoundaryLetter] at hncenter ⊢
  exact
    hne
      ((lpmTyping_eq_one_iff_boundary_only w).2 hall)

/--
Proposition 8.6, positive direction:
L_{±,e} is substitutable for the concrete four-element typing.
-/
theorem lpm_fixedHSubstitutable :
    FixedHSubstitutable lpmTyping LpmLanguage := by
  intro x y hxne hyne htype hshared
  rcases hshared with ⟨u, v, hxL, hyL⟩
  have hshared' :
      HaveSharedContext LpmLanguage x y :=
    ⟨u, v, hxL, hyL⟩

  cases hxType : lpmTyping.h x with
  | one =>
      have hyType : lpmTyping.h y = 1 := by
        calc
          lpmTyping.h y = lpmTyping.h x := htype.symm
          _ = 1 := hxType
      have hxb :
          ∀ t ∈ x, LpmBoundaryLetter t :=
        (lpmTyping_eq_one_iff_boundary_only x).1 hxType
      have hyb :
          ∀ t ∈ y, LpmBoundaryLetter t :=
        (lpmTyping_eq_one_iff_boundary_only y).1 hyType
      have hxy :
          x = y :=
        lpm_boundary_factors_eq
          hxne hyne hxb hyb hshared'
      subst y
      rfl

  | cd =>
      have hyType : lpmTyping.h y = cd := by
        calc
          lpmTyping.h y = lpmTyping.h x := htype.symm
          _ = cd := hxType
      have hxneOne : lpmTyping.h x ≠ 1 := by
        rw [hxType]
        decide
      have hyneOne : lpmTyping.h y ≠ 1 := by
        rw [hyType]
        decide
      obtain ⟨zx, hzxmem, hzxc⟩ :=
        exists_center_mem_of_typing_ne_one x hxneOne
      obtain ⟨zy, hzymem, hzyc⟩ :=
        exists_center_mem_of_typing_ne_one y hyneOne
      obtain ⟨r, i, j, s, hu, hxshape, hv⟩ :=
        lpm_factor_shape_of_center_mem
          hzxc hzxmem hxL
      obtain ⟨_r', i', j', _s', _hu', hyshape, _hv'⟩ :=
        lpm_factor_shape_of_center_mem
          hzyc hzymem hyL
      have hzxType : lpmLetterType zx = cd := by
        simpa [hxshape] using hxType
      have hzyType : lpmLetterType zy = cd := by
        simpa [hyshape] using hyType
      have hzxBranch : zx = c ∨ zx = d :=
        (lpmLetterType_eq_cd_iff zx).1 hzxType
      have hzyBranch : zy = c ∨ zy = d :=
        (lpmLetterType_eq_cd_iff zy).1 hzyType
      have hsharedX :
          List.replicate r a ++
              lpmOneCenter i zx j ++
              List.replicate s b ∈ LpmLanguage := by
        simpa [hu, hv, hxshape] using hxL
      have hsharedY :
          List.replicate r a ++
              lpmOneCenter i' zy j' ++
              List.replicate s b ∈ LpmLanguage := by
        simpa [hu, hv, hyshape] using hyL
      rw [hxshape, hyshape]
      apply Set.ext
      rintro ⟨p, q⟩
      constructor
      · intro hp
        obtain ⟨m, n, hpm, hqn⟩ :=
          lpm_distribution_context_shape hzxc hp
        subst p
        subst q
        have hpL :
            List.replicate m a ++
                lpmOneCenter i zx j ++
                List.replicate n b ∈ LpmLanguage := by
          simpa [Distribution] using hp
        have hyctx :=
          lpm_cd_power_context_fourth
            hzxBranch hzyBranch
            hsharedX hsharedY hpL
        simpa [Distribution] using hyctx
      · intro hp
        obtain ⟨m, n, hpm, hqn⟩ :=
          lpm_distribution_context_shape hzyc hp
        subst p
        subst q
        have hpL :
            List.replicate m a ++
                lpmOneCenter i' zy j' ++
                List.replicate n b ∈ LpmLanguage := by
          simpa [Distribution] using hp
        have hxctx :=
          lpm_cd_power_context_fourth
            hzyBranch hzxBranch
            hsharedY hsharedX hpL
        simpa [Distribution] using hxctx

  | ee =>
      have hyType : lpmTyping.h y = ee := by
        calc
          lpmTyping.h y = lpmTyping.h x := htype.symm
          _ = ee := hxType
      have hxneOne : lpmTyping.h x ≠ 1 := by
        rw [hxType]
        decide
      have hyneOne : lpmTyping.h y ≠ 1 := by
        rw [hyType]
        decide
      obtain ⟨zx, hzxmem, hzxc⟩ :=
        exists_center_mem_of_typing_ne_one x hxneOne
      obtain ⟨zy, hzymem, hzyc⟩ :=
        exists_center_mem_of_typing_ne_one y hyneOne
      obtain ⟨r, i, j, s, hu, hxshape, hv⟩ :=
        lpm_factor_shape_of_center_mem
          hzxc hzxmem hxL
      obtain ⟨_r', i', j', _s', _hu', hyshape, _hv'⟩ :=
        lpm_factor_shape_of_center_mem
          hzyc hzymem hyL
      have hzxType : lpmLetterType zx = ee := by
        simpa [hxshape] using hxType
      have hzyType : lpmLetterType zy = ee := by
        simpa [hyshape] using hyType
      have hzxe : zx = e :=
        (lpmLetterType_eq_ee_iff zx).1 hzxType
      have hzye : zy = e :=
        (lpmLetterType_eq_ee_iff zy).1 hzyType
      subst zx
      subst zy
      have hsharedX :
          List.replicate r a ++
              lpmOneCenter i e j ++
              List.replicate s b ∈ LpmLanguage := by
        simpa [hu, hv, hxshape] using hxL
      have hsharedY :
          List.replicate r a ++
              lpmOneCenter i' e j' ++
              List.replicate s b ∈ LpmLanguage := by
        simpa [hu, hv, hyshape] using hyL
      rw [hxshape, hyshape]
      apply Set.ext
      rintro ⟨p, q⟩
      constructor
      · intro hp
        obtain ⟨m, n, hpm, hqn⟩ :=
          lpm_distribution_context_shape
            (by simp [LpmCenterSymbol]) hp
        subst p
        subst q
        have hpL :
            List.replicate m a ++
                lpmOneCenter i e j ++
                List.replicate n b ∈ LpmLanguage := by
          simpa [Distribution] using hp
        have hyctx :=
          lpm_e_power_context_fourth
            hsharedX hsharedY hpL
        simpa [Distribution] using hyctx
      · intro hp
        obtain ⟨m, n, hpm, hqn⟩ :=
          lpm_distribution_context_shape
            (by simp [LpmCenterSymbol]) hp
        subst p
        subst q
        have hpL :
            List.replicate m a ++
                lpmOneCenter i' e j' ++
                List.replicate n b ∈ LpmLanguage := by
          simpa [Distribution] using hp
        have hxctx :=
          lpm_e_power_context_fourth
            hsharedY hsharedX hpL
        simpa [Distribution] using hxctx

  | zero =>
      have hxneOne : lpmTyping.h x ≠ 1 := by
        rw [hxType]
        decide
      obtain ⟨zx, hzxmem, hzxc⟩ :=
        exists_center_mem_of_typing_ne_one x hxneOne
      obtain ⟨_r, i, j, _s, _hu, hxshape, _hv⟩ :=
        lpm_factor_shape_of_center_mem
          hzxc hzxmem hxL
      have hzxType : lpmLetterType zx = zero := by
        simpa [hxshape] using hxType
      rcases hzxc with rfl | rfl | rfl <;>
        simp [lpmLetterType] at hzxType

end TCS1
end LeanCfgProject
