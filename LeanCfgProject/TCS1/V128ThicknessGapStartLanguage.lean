import LeanCfgProject.TCS1.V128ThicknessGapCore
import LeanCfgProject.TCS1.V128ErasureFlagTyping

/-!
# TCS #1 v128: universal-language and reachability bridge for the gap family

Models the full source-production shape of the fixed-typing exponential-gap
example: S₀ → U, U → a | c | U U | Eₙ D, D → c, and
E₀ → a, Eᵢ₊₁ → Eᵢ Eᵢ | c.

The E-fragment is the already checked ExponentialBranchYield relation.
The constructors of GapUniversalYield below implement U's four alternatives.
As source semantics, this proves the start language is {a,c}^+ for all n,
and the no-c exponential witness at Eₙ participates in a successful start
derivation through U → Eₙ D.

This does NOT yet establish the full actual finite SSBNF grammar's reduction,
trimming after typed refinement, or a theorem about its typed thickness.
-/

namespace LeanCfgProject
namespace TCS1

/-- U derivations in the complete exponential-gap family, at parameter n. -/
inductive GapUniversalYield (n : Nat) : List Bool → Prop
  | letterA : GapUniversalYield n [false]
  | letterC : GapUniversalYield n [true]
  | combine {u v : List Bool}
      (du : GapUniversalYield n u)
      (dv : GapUniversalYield n v) :
      GapUniversalYield n (u ++ v)
  | exponentialBranch {w : List Bool}
      (de : ExponentialBranchYield n w) :
      GapUniversalYield n (w ++ [true])

/-- S₀ → U: the full start language is the language of U. -/
def GapStartLanguage (n : Nat) : Set (List Bool) :=
  {w | GapUniversalYield n w}

/-- No U production produces the empty word. -/
theorem gapUniversalYield_nonempty
    {n : Nat} {w : List Bool}
    (d : GapUniversalYield n w) : w ≠ [] := by
  induction d with
  | letterA => simp
  | letterC => simp
  | @combine u v _du _dv ihU _ihV =>
      intro hnil
      have htake := congrArg (fun z : List Bool => z.take u.length) hnil
      have hu : u = [] := by simpa using htake
      exact ihU hu
  | exponentialBranch _ =>
      simp

/-- Every positive word is derived by U without even using the E_n D rule. -/
theorem gapUniversalYield_all_nonempty
    (n : Nat) (w : List Bool) (hw : w ≠ []) :
    GapUniversalYield n w := by
  induction w with
  | nil =>
      exact False.elim (hw rfl)
  | cons a tail ih =>
      cases tail with
      | nil =>
          cases a with
          | false => exact GapUniversalYield.letterA
          | true => exact GapUniversalYield.letterC
      | cons b bs =>
          have htail : (b :: bs : List Bool) ≠ [] := by simp
          have dtail := ih htail
          cases a with
          | false =>
              simpa using
                (GapUniversalYield.combine GapUniversalYield.letterA dtail)
          | true =>
              simpa using
                (GapUniversalYield.combine GapUniversalYield.letterC dtail)

/-- The complete family has the fixed language {a,c}^+ at every n. -/
theorem gapStartLanguage_eq_nonempty
    (n : Nat) :
    GapStartLanguage n = {w : List Bool | w ≠ []} := by
  ext w
  constructor
  · exact gapUniversalYield_nonempty
  · exact gapUniversalYield_all_nonempty n w

/-- E_n's exponential type-1 witness appears in a successful start tree. -/
theorem gapExponentialBranch_successful_start
    (n : Nat) :
    ∃ w : List Bool,
      ExponentialBranchYield n w ∧
      ExponentialBranchNoC w ∧
      w.length = 2 ^ n ∧
      (w ++ [true]) ∈ GapStartLanguage n := by
  obtain ⟨w, de, hnc, hlen⟩ :=
    exponentialBranch_has_noC_witness n
  exact ⟨w, de, hnc, hlen, GapUniversalYield.exponentialBranch de⟩

/-- Ordinary source thickness of every E_i is at most one. -/
theorem gapExponentialBranch_short_source (i : Nat) :
    ∃ w : List Bool,
      ExponentialBranchYield i w ∧ w.length = 1 :=
  exponentialBranch_has_short_yield i

/-- All c-free E_n yields have the same exponential length. -/
theorem gapExponentialBranch_all_noC_long
    (n : Nat) (w : List Bool)
    (de : ExponentialBranchYield n w)
    (hnc : ExponentialBranchNoC w) :
    2 ^ n ≤ w.length := by
  exact le_of_eq (exponentialBranch_noC_length de hnc).symm

/-- Explicit source-production count of the displayed schema:
    E₀: 1, Eᵢ (1≤i≤n): 2 each, U: 4, D: 1, S₀: 1. -/
def gapSourceRuleCount (n : Nat) : Nat := 2 * n + 7

/-- The source-production count is linearly bounded in the parameter. -/
theorem gapSourceRuleCount_linear (n : Nat) :
    gapSourceRuleCount n ≤ 9 * (n + 1) := by
  unfold gapSourceRuleCount
  omega

end TCS1
end LeanCfgProject
