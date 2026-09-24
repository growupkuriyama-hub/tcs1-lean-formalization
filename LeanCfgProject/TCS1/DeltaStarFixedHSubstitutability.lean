import LeanCfgProject.TCS1.DeltaStarFixedH

/-!
# TCS #1 v78: Delta-star fixed-h substitutability

This module closes the nonlinear fixed-h part of Proposition 9.1.  It uses
the parser invariants from `DeltaStarFixedH` and the finite boundary typing
from `DeltaStarTyping`.

The proof follows the v78 manuscript split.

* If a factor contains an internal `ba`, a shared positive context fixes its
  admissible entry height.  Any other accepting occurrence has the same entry
  height, and equality of first symbols synchronizes the first transition.
* If no internal `ba` occurs, the factor is of the form `a^p b^q`.
  Equality of first/last symbols selects the same pure/mixed shape branch,
  while equality of balance transfers successful scanning.
* Equality of balance and last symbols then identifies the exit parser state,
  so arbitrary contexts transfer in both directions.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/--
For a factor containing an internal `ba`, a shared accepting context
provides one successful entry state.  Any other successful occurrence of the
same factor has the same numerical entry height; equality of first symbols
then transfers the shared successful run of `y` to that new entry state.
-/
theorem scan_exists_of_containsBA_features
    {x y : Word Symbol}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hfirst : firstSymbol? x = firstSymbol? y)
    (hba : containsBA x = true)
    (hshared : HaveSharedContext Language x y)
    {q r : Mode}
    (hxscan : scan q x = some r) :
    ∃ r' : Mode, scan q y = some r' := by
  rcases hshared with ⟨u, v, hux, huy⟩
  obtain ⟨q0, rx, hu, hx0, _hvx⟩ :=
    scan_context_decompose hux
  obtain ⟨ry, hy0, _hvy⟩ :=
    scan_middle_of_context hu huy
  have hheight :
      modeHeight q = modeHeight q0 :=
    entry_height_unique_of_containsBA
      hba hxscan hx0
  cases x with
  | nil =>
      exact False.elim (hxne rfl)
  | cons sx xt =>
      cases y with
      | nil =>
          exact False.elim (hyne rfl)
      | cons sy yt =>
          have hsy : sx = sy := by
            simpa [firstSymbol?] using hfirst
          subst sy
          obtain ⟨px, hsx, _hxt⟩ :=
            scan_cons_success hxscan
          obtain ⟨p0x, hs0x, _hx0t⟩ :=
            scan_cons_success hx0
          obtain ⟨p0y, hs0y, hy0t⟩ :=
            scan_cons_success hy0
          have hpx : px = p0x :=
            step_eq_of_same_height
              hheight hsx hs0x
          have hp0 : p0x = p0y := by
            rw [hs0x] at hs0y
            exact Option.some.inj hs0y
          rw [hpx, hp0] at hsx
          refine ⟨ry, ?_⟩
          simp only [scan]
          rw [hsx]
          exact hy0t

/--
No-`ba` transfer lemma.  Such words have shape `a^p b^q`; first/last
symbols force `x` and `y` into the same pure-a, pure-b, or genuinely mixed
branch.  In the pure cases equal balance makes the words identical.  In the
mixed case the parser transfer lemma depends only on the common balance.
-/
theorem scan_exists_of_noBA_features
    {x y : Word Symbol}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hfirst : firstSymbol? x = firstSymbol? y)
    (hlast : lastSymbol? x = lastSymbol? y)
    (hbx : containsBA x = false)
    (hby : containsBA y = false)
    (hbal : balance x = balance y)
    {entry r : Mode}
    (hxscan : scan entry x = some r) :
    ∃ r' : Mode, scan entry y = some r' := by
  rcases noBA_nonempty_shape_cases hxne hbx with hxA | hxRest
  · rcases hxA with ⟨p, hp, hxw⟩
    rcases noBA_nonempty_shape_cases hyne hby with hyA | hyRest
    · rcases hyA with ⟨p', hp', hyw⟩
      have heq : p = p' := by
        have hb := hbal
        rw [hxw, hyw] at hb
        simp only [balance_replicate_a] at hb
        omega
      subst p'
      have hs := hxscan
      rw [hxw] at hs
      refine ⟨r, ?_⟩
      rw [hyw]
      exact hs
    · rcases hyRest with hyB | hyM
      · rcases hyB with ⟨q', hq', hyw⟩
        exfalso
        have hf := hfirst
        rw [hxw, hyw,
          firstSymbol_replicate_pos a hp,
          firstSymbol_replicate_pos b hq'] at hf
        simpa using hf
      · rcases hyM with ⟨p', q', hp', hq', hyw⟩
        exfalso
        have hl := hlast
        rw [hxw, hyw,
          lastSymbol_replicate_pos a hp,
          lastSymbol_mixed hq'] at hl
        simpa using hl
  · rcases hxRest with hxB | hxM
    · rcases hxB with ⟨q, hq, hxw⟩
      rcases noBA_nonempty_shape_cases hyne hby with hyA | hyRest
      · rcases hyA with ⟨p', hp', hyw⟩
        exfalso
        have hf := hfirst
        rw [hxw, hyw,
          firstSymbol_replicate_pos b hq,
          firstSymbol_replicate_pos a hp'] at hf
        simpa using hf
      · rcases hyRest with hyB | hyM
        · rcases hyB with ⟨q', hq', hyw⟩
          have heq : q = q' := by
            have hb := hbal
            rw [hxw, hyw] at hb
            simp only [balance_replicate_b] at hb
            omega
          subst q'
          have hs := hxscan
          rw [hxw] at hs
          refine ⟨r, ?_⟩
          rw [hyw]
          exact hs
        · rcases hyM with ⟨p', q', hp', hq', hyw⟩
          exfalso
          have hf := hfirst
          rw [hxw, hyw,
            firstSymbol_replicate_pos b hq,
            firstSymbol_mixed hp'] at hf
          simpa using hf
    · rcases hxM with ⟨p, q, hp, hq, hxw⟩
      rcases noBA_nonempty_shape_cases hyne hby with hyA | hyRest
      · rcases hyA with ⟨p', hp', hyw⟩
        exfalso
        have hl := hlast
        rw [hxw, hyw,
          lastSymbol_mixed hq,
          lastSymbol_replicate_pos a hp'] at hl
        simpa using hl
      · rcases hyRest with hyB | hyM
        · rcases hyB with ⟨q', hq', hyw⟩
          exfalso
          have hf := hfirst
          rw [hxw, hyw,
            firstSymbol_mixed hp,
            firstSymbol_replicate_pos b hq'] at hf
          simpa using hf
        · rcases hyM with ⟨p', q', hp', hq', hyw⟩
          have hdiff :
              (p : Int) - (q : Int) =
                (p' : Int) - (q' : Int) := by
            have hb := hbal
            rw [hxw, hyw] at hb
            simp only [balance_append,
              balance_replicate_a,
              balance_replicate_b] at hb
            omega
          have hs := hxscan
          rw [hxw] at hs
          obtain ⟨r', hr'⟩ :=
            scan_mixed_exists_of_same_balance
              hp hq hp' hq' hdiff hs
          refine ⟨r', ?_⟩
          rw [hyw]
          exact hr'

/-- Successful scanning transfers under the four paper-facing factor features. -/
theorem scan_exists_of_features
    {x y : Word Symbol}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hfirst : firstSymbol? x = firstSymbol? y)
    (hlast : lastSymbol? x = lastSymbol? y)
    (hba : containsBA x = containsBA y)
    (hbal : balance x = balance y)
    (hshared : HaveSharedContext Language x y)
    {q r : Mode}
    (hxscan : scan q x = some r) :
    ∃ r' : Mode, scan q y = some r' := by
  cases hbx : containsBA x with
  | false =>
      have hby : containsBA y = false := by
        calc
          containsBA y = containsBA x := hba.symm
          _ = false := hbx
      exact
        scan_exists_of_noBA_features
          hxne hyne hfirst hlast
          hbx hby hbal hxscan
  | true =>
      exact
        scan_exists_of_containsBA_features
          hxne hyne hfirst hbx
          hshared hxscan

/--
The transferred run exits in the same parser state, because equal balance and
equal last symbol determine the successful exit mode once the entry mode is
fixed.
-/
theorem scan_transfer_same_exit_of_features
    {x y : Word Symbol}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hfirst : firstSymbol? x = firstSymbol? y)
    (hlast : lastSymbol? x = lastSymbol? y)
    (hba : containsBA x = containsBA y)
    (hbal : balance x = balance y)
    (hshared : HaveSharedContext Language x y)
    {q r : Mode}
    (hxscan : scan q x = some r) :
    scan q y = some r := by
  obtain ⟨r', hyr⟩ :=
    scan_exists_of_features
      hxne hyne hfirst hlast hba hbal
      hshared hxscan
  have hre : r = r' :=
    scan_final_eq_of_balance_last
      hxne hyne hbal hlast hxscan hyr
  rw [← hre] at hyr
  exact hyr

/--
The nonlinear parser language is substitutable for the finite homomorphism
`h_star` encoded by `starTyping`.
-/
theorem deltaStar_fixedHSubstitutable :
    FixedHSubstitutable starTyping Language := by
  intro x y hxne hyne htype hshared
  rcases starTyping_eq_features htype with
    ⟨hfirst, hlast, hba⟩
  have hbal : balance x = balance y :=
    balance_eq_of_sharedContext hshared
  have hsharedYX :
      HaveSharedContext Language y x := by
    rcases hshared with ⟨u, v, hxL, hyL⟩
    exact ⟨u, v, hyL, hxL⟩
  apply Set.ext
  intro c
  constructor
  · intro hc
    change c.1 ++ x ++ c.2 ∈ Language at hc
    obtain ⟨q, r, hu, hx, hv⟩ :=
      scan_context_decompose hc
    have hy : scan q y = some r :=
      scan_transfer_same_exit_of_features
        hxne hyne hfirst hlast hba hbal
        hshared hx
    change c.1 ++ y ++ c.2 ∈ Language
    exact mem_of_context_scans hu hy hv
  · intro hc
    change c.1 ++ y ++ c.2 ∈ Language at hc
    obtain ⟨q, r, hu, hy, hv⟩ :=
      scan_context_decompose hc
    have hx : scan q x = some r :=
      scan_transfer_same_exit_of_features
        hyne hxne hfirst.symm hlast.symm
        hba.symm hbal.symm hsharedYX hy
    change c.1 ++ x ++ c.2 ∈ Language
    exact mem_of_context_scans hu hx hv

/-- Paper-facing semantic separation package for the Delta-star example. -/
theorem deltaStar_fixedH_and_outside_all_fixedWindows :
    FixedHSubstitutable starTyping Language ∧
      ∀ k l : Nat,
        ¬ FixedWindowSubstitutable k l Language := by
  exact
    ⟨deltaStar_fixedHSubstitutable,
      not_fixedWindowSubstitutable⟩

end DeltaStar
end TCS1
end LeanCfgProject
