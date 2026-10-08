import LeanCfgProject.TCS1.V128ThicknessGapStartLanguage

/-!
# TCS #1 v128: connect the exponential E-branch to a fixed two-element typing

Use the zero monoid ErasureFlag (erased = 1, present = zero) and the
nonerasing marker of c: each false/a maps to the empty word,
each true/c survives filtering. The resulting erasure-flag homomorphism
is the manuscript's fixed h_c: a maps to 1 and c maps to zero.

The fibre h_c^-1(1) is exactly the c-free word set. Thus the checked
E_n-branch length bound is a genuine fixed-typing fibre lower bound,
and its witness is used along a successful start derivation.

This is not yet a verified global typed-thickness bound after trimming
of a concrete reduced SSBNF grammar.
-/

namespace LeanCfgProject
namespace TCS1

/-- The word morphism retaining occurrences of the marker c. -/
def gapMarkerImage (w : List Bool) : List Bool :=
  w.filter id

theorem gapMarkerImage_nil :
    gapMarkerImage [] = [] := by
  rfl

theorem gapMarkerImage_append (u v : List Bool) :
    gapMarkerImage (u ++ v) =
      gapMarkerImage u ++ gapMarkerImage v := by
  simp [gapMarkerImage]

/-- The manuscript's fixed two-element zero typing h_c. -/
def gapCZeroTyping : FixedFiniteMonoidHom Bool ErasureFlag :=
  erasureFlagTyping gapMarkerImage gapMarkerImage_nil gapMarkerImage_append

/-- A filtered marker word is empty exactly when the original contains no c. -/
theorem gapMarkerImage_nil_iff_noC (w : List Bool) :
    gapMarkerImage w = [] ↔ ExponentialBranchNoC w := by
  induction w with
  | nil =>
      simp [gapMarkerImage, ExponentialBranchNoC]
  | cons b tail ih =>
      cases b with
      | false =>
          simpa [gapMarkerImage, ExponentialBranchNoC] using ih
      | true =>
          simp [gapMarkerImage, ExponentialBranchNoC]

/-- Equality with the typing identity is exactly absence of c. -/
theorem gapCZeroTyping_one_iff_noC (w : List Bool) :
    gapCZeroTyping.h w = (1 : ErasureFlag) ↔
      ExponentialBranchNoC w := by
  change erasureFlagValue gapMarkerImage w = ErasureFlag.erased ↔
    ExponentialBranchNoC w
  exact (erasureFlagValue_erased_iff gapMarkerImage w).trans
    (gapMarkerImage_nil_iff_noC w)

/-- Every unit-fibre yield of E_n has exponentially large length. -/
theorem gapExponentialBranch_unit_fibre_length
    (n : Nat) (w : List Bool)
    (de : ExponentialBranchYield n w)
    (ht : gapCZeroTyping.h w = (1 : ErasureFlag)) :
    w.length = 2 ^ n := by
  exact exponentialBranch_noC_length de
    ((gapCZeroTyping_one_iff_noC w).mp ht)

/-- Such a unit-fibre witness occurs inside a successful U → E_n D tree. -/
theorem gapExponentialBranch_unit_fibre_reachable
    (n : Nat) :
    ∃ w : List Bool,
      ExponentialBranchYield n w ∧
      gapCZeroTyping.h w = (1 : ErasureFlag) ∧
      w.length = 2 ^ n ∧
      (w ++ [true]) ∈ GapStartLanguage n := by
  obtain ⟨w, d, hnc, hw, hs⟩ := gapExponentialBranch_successful_start n
  exact ⟨w, d, (gapCZeroTyping_one_iff_noC w).mpr hnc, hw, hs⟩

end TCS1
end LeanCfgProject
