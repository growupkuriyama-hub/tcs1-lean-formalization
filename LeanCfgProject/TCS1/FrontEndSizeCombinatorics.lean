import LeanCfgProject.TCS1.SSBNFNormalizationCombinatorics

/-!
# TCS #1 v66: linear-size bookkeeping for terminal isolation and binarization

Appendix A uses a linear-size front end before epsilon elimination:

1. terminal wrappers contribute at most linearly many fresh states/rules;
2. right-associated binarization of a right-hand side of length m creates at
   most m fresh suffix states and at most m + 1 structural rules.

This file formalizes that counting layer independently of grammar semantics.
It is deliberately parameterized by a finite family of source productions and
their right-hand-side lengths, so it can later be attached to any concrete
finite CFG encoding.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FrontEndSizeCombinatorics

variable {P : Type u}
variable {X : Type v}

/-- Number of fresh suffix states needed by right-associated binarization. -/
def freshBinarizationStateCount (m : Nat) : Nat :=
  m - 2

/-- Number of structural rules contributed by one binarized source rule. -/
def binarizedStructuralRuleCount (m : Nat) : Nat :=
  if m ≤ 2 then 1 else m - 1

/-- Fresh suffix states are bounded by the source RHS length. -/
theorem freshBinarizationStateCount_le
    (m : Nat) :
    freshBinarizationStateCount m ≤ m := by
  unfold freshBinarizationStateCount
  exact Nat.sub_le _ _

/-- One source production contributes at most m+1 binary-front-end rules. -/
theorem binarizedStructuralRuleCount_le_succ
    (m : Nat) :
    binarizedStructuralRuleCount m ≤ m + 1 := by
  unfold binarizedStructuralRuleCount
  by_cases h : m ≤ 2
  · simp [h]
  · simp [h]
    omega

/-- Total source right-hand-side length of a finite production family. -/
def totalRhsLength
    [DecidableEq P]
    (rules : Finset P)
    (rhs : P → List X) : Nat :=
  ∑ r ∈ rules, (rhs r).length

/-- Total number of fresh suffix states, counted with production provenance. -/
def totalFreshBinarizationStates
    [DecidableEq P]
    (rules : Finset P)
    (rhs : P → List X) : Nat :=
  ∑ r ∈ rules,
    freshBinarizationStateCount (rhs r).length

/-- Total number of structural rules after right-associated binarization. -/
def totalBinarizedStructuralRules
    [DecidableEq P]
    (rules : Finset P)
    (rhs : P → List X) : Nat :=
  ∑ r ∈ rules,
    binarizedStructuralRuleCount (rhs r).length

/-- Summed fresh-state count is at most total RHS length. -/
theorem totalFreshBinarizationStates_le_rhsLength
    [DecidableEq P]
    (rules : Finset P)
    (rhs : P → List X) :
    totalFreshBinarizationStates rules rhs ≤
      totalRhsLength rules rhs := by
  unfold totalFreshBinarizationStates totalRhsLength
  apply Finset.sum_le_sum
  intro r hr
  exact freshBinarizationStateCount_le (rhs r).length

/--
Summed structural-rule count is at most the number of source productions plus
the total source RHS length.
-/
theorem totalBinarizedStructuralRules_le
    [DecidableEq P]
    (rules : Finset P)
    (rhs : P → List X) :
    totalBinarizedStructuralRules rules rhs ≤
      rules.card + totalRhsLength rules rhs := by
  unfold totalBinarizedStructuralRules totalRhsLength
  calc
    (∑ r ∈ rules,
      binarizedStructuralRuleCount (rhs r).length)
      ≤
    ∑ r ∈ rules, ((rhs r).length + 1) := by
      apply Finset.sum_le_sum
      intro r hr
      exact
        binarizedStructuralRuleCount_le_succ
          (rhs r).length
    _ =
      (∑ r ∈ rules, (rhs r).length) + rules.card := by
        simp [Finset.sum_add_distrib, Nat.add_comm]
    _ =
      rules.card + (∑ r ∈ rules, (rhs r).length) := by
        omega

/--
If source productions and total RHS length are linear in input size, then the
binarized structural-rule family is linear as well.
-/
theorem totalBinarizedStructuralRules_linear
    [DecidableEq P]
    (rules : Finset P)
    (rhs : P → List X)
    (cP cR n : Nat)
    (hP : rules.card ≤ cP * n)
    (hR : totalRhsLength rules rhs ≤ cR * n) :
    totalBinarizedStructuralRules rules rhs ≤
      (cP + cR) * n := by
  have hfront :=
    totalBinarizedStructuralRules_le rules rhs
  calc
    totalBinarizedStructuralRules rules rhs
      ≤ rules.card + totalRhsLength rules rhs := hfront
    _ ≤ cP * n + cR * n := Nat.add_le_add hP hR
    _ = (cP + cR) * n := by ring

/--
If original states, terminal wrappers, and total source RHS length are all
linear, then the old+wrapper+fresh-suffix state space is linear.
-/
theorem frontEndStateCount_linear
    [DecidableEq P]
    (rules : Finset P)
    (rhs : P → List X)
    (oldStates wrappers cV cW cR n : Nat)
    (hV : oldStates ≤ cV * n)
    (hW : wrappers ≤ cW * n)
    (hR : totalRhsLength rules rhs ≤ cR * n) :
    oldStates + wrappers +
        totalFreshBinarizationStates rules rhs
      ≤
    (cV + cW + cR) * n := by
  have hFresh :
      totalFreshBinarizationStates rules rhs ≤ cR * n :=
    le_trans
      (totalFreshBinarizationStates_le_rhsLength rules rhs)
      hR
  calc
    oldStates + wrappers +
        totalFreshBinarizationStates rules rhs
      ≤ cV * n + cW * n + cR * n := by omega
    _ = (cV + cW + cR) * n := by ring

/--
Including one wrapper rule per terminal wrapper, the complete front-end rule
count remains linear.
-/
theorem frontEndRuleCount_linear
    [DecidableEq P]
    (rules : Finset P)
    (rhs : P → List X)
    (wrappers cP cR cW n : Nat)
    (hP : rules.card ≤ cP * n)
    (hR : totalRhsLength rules rhs ≤ cR * n)
    (hW : wrappers ≤ cW * n) :
    totalBinarizedStructuralRules rules rhs + wrappers
      ≤
    (cP + cR + cW) * n := by
  have hBin :
      totalBinarizedStructuralRules rules rhs ≤
        (cP + cR) * n :=
    totalBinarizedStructuralRules_linear
      rules rhs cP cR n hP hR
  calc
    totalBinarizedStructuralRules rules rhs + wrappers
      ≤ (cP + cR) * n + cW * n :=
        Nat.add_le_add hBin hW
    _ = (cP + cR + cW) * n := by ring

end FrontEndSizeCombinatorics

end TCS1
end LeanCfgProject
