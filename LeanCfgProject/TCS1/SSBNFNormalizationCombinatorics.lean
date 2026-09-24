import LeanCfgProject.TCS1.SSBNFThicknessBounds

/-!
# TCS #1: combinatorics of the SSBNF normalization pipeline

This file formalizes the finite-counting claims used in the appendix proof of
the polynomial thickness-preserving SSBNF normalization.

The manuscript deliberately performs terminal isolation and binarization
*before* non-start epsilon elimination.  Once every non-start structural rule
is binary, eliminating epsilon from one binary rule A -> B C can create only

  A -> B C,  A -> B,  A -> C,

according to nullability of the children.  Thus there is no nullable-subset
explosion.  After that, unit elimination copies each non-unit production to
each unit-reachable source; the raw candidate space is a Cartesian product of
sources and non-unit productions and is therefore quadratic when both factors
are linear-size.

This module checks those two counting facts and the resulting polynomial
composition.  It intentionally stays at the rule-count level; semantic
preservation of the standard grammar transformations is a separate layer.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section SSBNFNormalizationCombinatorics

variable {N : Type u}

/-- The three possible nonempty right-hand-side shapes contributed by one
binary rule during non-start epsilon elimination. -/
inductive BinaryNullableVariant (N : Type u)
  | keep : N → N → BinaryNullableVariant N
  | dropLeft : N → BinaryNullableVariant N
  | dropRight : N → BinaryNullableVariant N
deriving DecidableEq

/--
Candidate variants of a binary right-hand side B C after deleting nullable
children.  The original binary rule is always kept; a unit variant is added
for each nullable child.
-/
def leftNullableVariant
    [DecidableEq N]
    (nullable : N → Bool)
    (B C : N) :
    Finset (BinaryNullableVariant N) :=
  if nullable B = true then
    {BinaryNullableVariant.dropLeft C}
  else
    ∅

def rightNullableVariant
    [DecidableEq N]
    (nullable : N → Bool)
    (B C : N) :
    Finset (BinaryNullableVariant N) :=
  if nullable C = true then
    {BinaryNullableVariant.dropRight B}
  else
    ∅

def binaryNullableVariants
    [DecidableEq N]
    (nullable : N → Bool)
    (B C : N) :
    Finset (BinaryNullableVariant N) :=
  insert (BinaryNullableVariant.keep B C)
    (leftNullableVariant nullable B C ∪
     rightNullableVariant nullable B C)

/-- One binary rule produces at most three nonempty variants. -/
theorem binaryNullableVariants_card_le_three
    [DecidableEq N]
    (nullable : N → Bool)
    (B C : N) :
    (binaryNullableVariants nullable B C).card ≤ 3 := by
  by_cases hB : nullable B = true
  · by_cases hC : nullable C = true
    · simp [binaryNullableVariants, leftNullableVariant,
        rightNullableVariant, hB, hC]
    · simp [binaryNullableVariants, leftNullableVariant,
        rightNullableVariant, hB, hC]
  · by_cases hC : nullable C = true
    · simp [binaryNullableVariants, leftNullableVariant,
        rightNullableVariant, hB, hC]
    · simp [binaryNullableVariants, leftNullableVariant,
        rightNullableVariant, hB, hC]

/--
Summed with multiplicity, epsilon elimination contributes at most three
candidate nonempty rules per original binary rule.
-/
theorem total_binary_nullable_candidates_le
    {R : Type v}
    [DecidableEq N] [DecidableEq R]
    (rules : Finset R)
    (left right : R → N)
    (nullable : N → Bool) :
    (∑ r ∈ rules,
      (binaryNullableVariants nullable (left r) (right r)).card)
      ≤ 3 * rules.card := by
  calc
    (∑ r ∈ rules,
      (binaryNullableVariants nullable (left r) (right r)).card)
      ≤ ∑ _r ∈ rules, 3 := by
        apply Finset.sum_le_sum
        intro r hr
        exact binaryNullableVariants_card_le_three nullable (left r) (right r)
    _ = 3 * rules.card := by
        simp [Nat.mul_comm]

/--
The raw unit-elimination copy space: every possible source nonterminal paired
with every non-unit production.  Reachability filtering can only reduce this
space.
-/
def unitCopyCandidates
    {Rule : Type v}
    [DecidableEq N] [DecidableEq Rule]
    (sources : Finset N)
    (nonUnitRules : Finset Rule) :
    Finset (N × Rule) :=
  sources.product nonUnitRules

@[simp] theorem unitCopyCandidates_card
    {Rule : Type v}
    [DecidableEq N] [DecidableEq Rule]
    (sources : Finset N)
    (nonUnitRules : Finset Rule) :
    (unitCopyCandidates sources nonUnitRules).card =
      sources.card * nonUnitRules.card := by
  simp [unitCopyCandidates]

/--
If the number of source nonterminals and pre-unit-elimination non-unit rules
are both linear in the original grammar size n, then the raw copy space is
quadratic in n.
-/
theorem unitCopyCandidates_quadratic_bound
    {Rule : Type v}
    [DecidableEq N] [DecidableEq Rule]
    (sources : Finset N)
    (nonUnitRules : Finset Rule)
    (cV cP n : Nat)
    (hV : sources.card ≤ cV * n)
    (hP : nonUnitRules.card ≤ cP * n) :
    (unitCopyCandidates sources nonUnitRules).card
      ≤ (cV * cP) * n^2 := by
  rw [unitCopyCandidates_card]
  have hmul :
      sources.card * nonUnitRules.card
        ≤ (cV * n) * (cP * n) :=
    Nat.mul_le_mul hV hP
  calc
    sources.card * nonUnitRules.card
      ≤ (cV * n) * (cP * n) := hmul
    _ = (cV * cP) * n^2 := by ring

/--
After binary epsilon elimination, a linear number p of binary rules gives at
most 3p candidate structural rules.  Adding t already-terminal rules remains
linear.
-/
theorem post_epsilon_nonunit_rule_bound
    {p t cP cT n : Nat}
    (hp : p ≤ cP * n)
    (ht : t ≤ cT * n) :
    t + 3 * p ≤ (cT + 3 * cP) * n := by
  calc
    t + 3 * p
      ≤ cT * n + 3 * (cP * n) := by omega
    _ = (cT + 3 * cP) * n := by ring

/--
Combining the previous two manuscript estimates gives an explicit quadratic
upper envelope for the number of raw rules after unit elimination.
-/
theorem normalization_rule_count_quadratic
    {v p t cV cP cT n : Nat}
    (hv : v ≤ cV * n)
    (hp : p ≤ cP * n)
    (ht : t ≤ cT * n) :
    v * (t + 3 * p)
      ≤ (cV * (cT + 3 * cP)) * n^2 := by
  have hNonUnit :
      t + 3 * p ≤ (cT + 3 * cP) * n :=
    post_epsilon_nonunit_rule_bound hp ht
  have hmul :
      v * (t + 3 * p)
        ≤ (cV * n) * ((cT + 3 * cP) * n) :=
    Nat.mul_le_mul hv hNonUnit
  calc
    v * (t + 3 * p)
      ≤ (cV * n) * ((cT + 3 * cP) * n) := hmul
    _ = (cV * (cT + 3 * cP)) * n^2 := by ring

/--
There is no exponential nullable-subset factor in the binary-first pipeline:
the local factor is the absolute constant three.
-/
theorem binary_first_nullable_factor_constant
    [DecidableEq N]
    (nullable : N → Bool)
    (B C : N) :
    ∃ c : Nat,
      c = 3 ∧
      (binaryNullableVariants nullable B C).card ≤ c := by
  exact ⟨3, rfl, binaryNullableVariants_card_le_three nullable B C⟩

end SSBNFNormalizationCombinatorics

end TCS1
end LeanCfgProject
