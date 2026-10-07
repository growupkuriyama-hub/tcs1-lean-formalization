import LeanCfgProject.TCS1.DeltaStarDisplayedGrammar
import Mathlib.Tactic

/-!
# TCS #1 v126: exact balance / zero-height characterization of Delta-star

This file formalizes the displayed manuscript characterization (star):

  w in Delta* iff
  every prefix has nonnegative balance,
  total balance is zero, and
  every occurrence of ba is met at height zero.

"Height of ba" means the balance of the prefix ending at that b.
The proof is tied directly to the deterministic parser already used by the
Delta-star formalization.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/-- Manuscript condition underline-beta(w) >= 0, written without introducing
an explicit minimum over a finite prefix set. -/
def PrefixBalanceNonnegative
    (w : Word Symbol) : Prop :=
  ∀ p r : Word Symbol,
    w = p ++ r →
    0 ≤ balance p

/-- Every occurrence of ba is at global height zero.  If
w = u ++ b a ++ v, the relevant height is beta(u b). -/
def EveryBAAtHeightZero
    (w : Word Symbol) : Prop :=
  ∀ u v : Word Symbol,
    w = u ++ b :: a :: v →
    balance (u ++ [b]) = 0

/-- A successful complete scan implies successful scanning of every prefix. -/
theorem scan_zero_prefix_success
    {w p r : Word Symbol}
    (hw : scan .zero w = some .zero)
    (hpr : w = p ++ r) :
    ∃ q : Mode,
      scan .zero p = some q := by
  rw [hpr, scan_append] at hw
  cases hp : scan .zero p with
  | none =>
      rw [hp] at hw
      cases hw
  | some q =>
      exact ⟨q, rfl⟩

/-- Parser acceptance implies the manuscript's nonnegative-prefix condition. -/
theorem language_prefixBalanceNonnegative
    {w : Word Symbol}
    (hw : w ∈ Language) :
    PrefixBalanceNonnegative w := by
  intro p r hpr
  obtain ⟨q, hp⟩ :=
    scan_zero_prefix_success hw hpr
  have hh : modeHeight q = balance p := by
    simpa [modeHeight] using (scan_height hp)
  have hnon : 0 ≤ modeHeight q :=
    modeHeight_nonneg q
  omega

/-- Parser acceptance implies that every ba transition occurs at height zero. -/
theorem language_everyBAAtHeightZero
    {w : Word Symbol}
    (hw : w ∈ Language) :
    EveryBAAtHeightZero w := by
  intro u v hshape
  have hwhole : scan .zero (u ++ b :: a :: v) = some .zero := by
    rw [← hshape]
    exact hw
  rw [scan_append] at hwhole
  cases hu : scan .zero u with
  | none =>
      rw [hu] at hwhole
      cases hwhole
  | some q =>
      rw [hu] at hwhole
      simp only at hwhole
      obtain ⟨p, hb, hafterb⟩ :=
        scan_cons_success hwhole
      obtain ⟨r, ha, hav⟩ :=
        scan_cons_success hafterb
      have hq : modeHeight q = 1 :=
        step_b_then_a_entry_height_one hb ha
      have hbu := scan_height hu
      have hbalU : balance u = 1 := by
        simp [modeHeight] at hbu hq
        omega
      simp [balance_append, hbalU]

/-- Exact forward half of the displayed (star) characterization. -/
theorem language_implies_balance_zeroHeight_criterion
    {w : Word Symbol}
    (hw : w ∈ Language) :
    PrefixBalanceNonnegative w ∧
      balance w = 0 ∧
      EveryBAAtHeightZero w := by
  exact
    ⟨language_prefixBalanceNonnegative hw,
      balance_mem_zero hw,
      language_everyBAAtHeightZero hw⟩

/-- A word whose recorded last symbol is b ends in b. -/
theorem exists_append_b_of_lastSymbol
    {p : Word Symbol}
    (hl : lastSymbol? p = some b) :
    ∃ u : Word Symbol,
      p = u ++ [b] := by
  induction p with
  | nil =>
      simp [lastSymbol?] at hl
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [lastSymbol?, lastFrom] at hl
          subst x
          exact ⟨[], rfl⟩
      | cons y ys =>
          have htail :
              lastSymbol? (y :: ys) = some b := by
            simpa [lastSymbol?, lastFrom] using hl
          obtain ⟨u, hu⟩ := ih htail
          refine ⟨x :: u, ?_⟩
          simp [hu]

/-- If a successful scan from zero ends in a falling state, the processed
nonempty word ends in b. -/
theorem exists_append_b_of_scan_zero_falling
    {p : Word Symbol} {n : Nat}
    (hp : scan .zero p = some (.falling n)) :
    ∃ u : Word Symbol,
      p = u ++ [b] := by
  have hpne : p ≠ [] := by
    intro hnil
    subst p
    simp [scan] at hp
  cases hl : lastSymbol? p with
  | none =>
      have : p = [] :=
        (lastSymbol_eq_none_iff p).1 hl
      exact False.elim (hpne this)
  | some s =>
      cases s with
      | a =>
          obtain ⟨m, hm⟩ :=
            scan_result_of_last_a
              hpne hl hp
          cases hm
      | b =>
          exact exists_append_b_of_lastSymbol hl

/-- One-step extension of a successful processed prefix. -/
theorem scan_zero_snoc
    {p : Word Symbol}
    {q q' : Mode}
    {s : Symbol}
    (hp : scan .zero p = some q)
    (hs : step q s = some q') :
    scan .zero (p ++ [s]) = some q' := by
  rw [scan_append, hp]
  simp [scan, hs]

/--
Under the two local manuscript conditions, the deterministic parser can never
get stuck while extending a processed prefix.
-/
theorem scan_suffix_success_of_criterion
    (w : Word Symbol)
    (hnon : PrefixBalanceNonnegative w)
    (hba : EveryBAAtHeightZero w) :
    ∀ (rest pref : Word Symbol) (q : Mode),
      w = pref ++ rest →
      scan .zero pref = some q →
      ∃ r : Mode, scan q rest = some r := by
  intro rest
  induction rest with
  | nil =>
      intro pref q hshape hp
      exact ⟨q, rfl⟩
  | cons s tail ih =>
      intro pref q hshape hp
      cases q with
      | zero =>
          cases s with
          | a =>
              have hp' :
                  scan .zero (pref ++ [a]) =
                    some (.rising 0) :=
                scan_zero_snoc hp (by rfl)
              have hshape' :
                  w = (pref ++ [a]) ++ tail := by
                rw [hshape]
                simp [List.append_assoc]
              obtain ⟨r, hr⟩ :=
                ih (pref ++ [a]) (.rising 0)
                  hshape' hp'
              refine ⟨r, ?_⟩
              simp only [scan, step]
              exact hr
          | b =>
              have hpheight := scan_height hp
              have hpbal : balance pref = 0 := by
                simp [modeHeight] at hpheight
                omega
              have hprefix :
                  0 ≤ balance (pref ++ [b]) :=
                hnon (pref ++ [b]) tail (by
                  rw [hshape]
                  simp [List.append_assoc])
              simp [balance_append, hpbal] at hprefix
      | rising n =>
          cases s with
          | a =>
              have hp' :
                  scan .zero (pref ++ [a]) =
                    some (.rising (n + 1)) :=
                scan_zero_snoc hp (by rfl)
              have hshape' :
                  w = (pref ++ [a]) ++ tail := by
                rw [hshape]
                simp [List.append_assoc]
              obtain ⟨r, hr⟩ :=
                ih (pref ++ [a]) (.rising (n + 1))
                  hshape' hp'
              refine ⟨r, ?_⟩
              simp only [scan, step]
              exact hr
          | b =>
              cases n with
              | zero =>
                  have hp' :
                      scan .zero (pref ++ [b]) =
                        some .zero :=
                    scan_zero_snoc hp (by rfl)
                  have hshape' :
                      w = (pref ++ [b]) ++ tail := by
                    rw [hshape]
                    simp [List.append_assoc]
                  obtain ⟨r, hr⟩ :=
                    ih (pref ++ [b]) .zero
                      hshape' hp'
                  refine ⟨r, ?_⟩
                  simp only [scan, step]
                  exact hr
              | succ n =>
                  have hp' :
                      scan .zero (pref ++ [b]) =
                        some (.falling n) :=
                    scan_zero_snoc hp (by rfl)
                  have hshape' :
                      w = (pref ++ [b]) ++ tail := by
                    rw [hshape]
                    simp [List.append_assoc]
                  obtain ⟨r, hr⟩ :=
                    ih (pref ++ [b]) (.falling n)
                      hshape' hp'
                  refine ⟨r, ?_⟩
                  simp only [scan, step]
                  exact hr
      | falling n =>
          cases s with
          | a =>
              obtain ⟨u, hpEnd⟩ :=
                exists_append_b_of_scan_zero_falling hp
              have hzero :
                  balance (u ++ [b]) = 0 := by
                apply hba u tail
                rw [hshape, hpEnd]
                simp [List.append_assoc]
              have hpheight := scan_height hp
              rw [hpEnd] at hpheight
              simp [modeHeight, balance_append] at hpheight hzero
              omega
          | b =>
              cases n with
              | zero =>
                  have hp' :
                      scan .zero (pref ++ [b]) =
                        some .zero :=
                    scan_zero_snoc hp (by rfl)
                  have hshape' :
                      w = (pref ++ [b]) ++ tail := by
                    rw [hshape]
                    simp [List.append_assoc]
                  obtain ⟨r, hr⟩ :=
                    ih (pref ++ [b]) .zero
                      hshape' hp'
                  refine ⟨r, ?_⟩
                  simp only [scan, step]
                  exact hr
              | succ n =>
                  have hp' :
                      scan .zero (pref ++ [b]) =
                        some (.falling n) :=
                    scan_zero_snoc hp (by rfl)
                  have hshape' :
                      w = (pref ++ [b]) ++ tail := by
                    rw [hshape]
                    simp [List.append_assoc]
                  obtain ⟨r, hr⟩ :=
                    ih (pref ++ [b]) (.falling n)
                      hshape' hp'
                  refine ⟨r, ?_⟩
                  simp only [scan, step]
                  exact hr

/-- Reverse half of the manuscript criterion. -/
theorem balance_zeroHeight_criterion_implies_language
    {w : Word Symbol}
    (hnon : PrefixBalanceNonnegative w)
    (hbal : balance w = 0)
    (hba : EveryBAAtHeightZero w) :
    w ∈ Language := by
  obtain ⟨r, hr⟩ :=
    scan_suffix_success_of_criterion
      w hnon hba w [] .zero
      (by simp) (by rfl)
  have hh := scan_height hr
  have hrzero : r = .zero := by
    cases r with
    | zero => rfl
    | rising n =>
        simp [modeHeight, hbal] at hh
        omega
    | falling n =>
        simp [modeHeight, hbal] at hh
        omega
  subst r
  exact hr

/-- Exact Lean statement of the displayed manuscript characterization (star). -/
theorem language_iff_balance_zeroHeight_criterion
    (w : Word Symbol) :
    w ∈ Language ↔
      PrefixBalanceNonnegative w ∧
      balance w = 0 ∧
      EveryBAAtHeightZero w := by
  constructor
  · exact language_implies_balance_zeroHeight_criterion
  · rintro ⟨hnon, hbal, hba⟩
    exact
      balance_zeroHeight_criterion_implies_language
        hnon hbal hba

end DeltaStar
end TCS1
end LeanCfgProject
