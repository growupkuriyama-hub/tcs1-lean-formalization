import LeanCfgProject.TCS1.V128SubstringBinarySplitSlots

/-!
# TCS #1 v135: literal output size of the actual v116 rule tables

`thm:poly-build` (v135) states that `B_h(K)` is constructible in time
polynomial in `‖K‖`; its proof sketches an `O(n_K^4)` bound whose last step
is: "even if factor strings are written literally in productions, each
production has encoding length `O(n_K)`, so the grammar can be … written
explicitly in `O(n_K^4)` time".

This module proves the **output-writing component** of that accounting for
the *actual* verified v116 tables (not a conditional interface):

* every observed factor has length `< n_K`;
* the literal encoding of every (B), (U), (L), (S), (ε) rule is `O(n_K)`;
* the **total literal length of all emitted rules** is at most
  `(2|Σ| + 7) · (n_K + 1)^4` (`v116LiteralOutputLength_le_quartic`);
* together with the already verified cubic candidate count, the combined
  "scan every candidate once + write every rule literally" budget is
  `O(n_K^4)` (`v116ScanAndWriteBudget_le_quartic`).

**Scope.**  This is an output-size and scan-count statement in the same
combinatorial cost convention as the v79 `MaterializedProductionCost`
module.  It does **not** formalize the preprocessing that produces canonical
identifiers for equal factors/contexts and the cached `h`-types (the
manuscript's "after preprocessing … constant-time" step), nor a machine
model; the full `O(n_K^4)` *time* theorem therefore remains open.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V135LiteralOutputSize

variable {α : Type u} {M : Type v}
variable [Fintype α] [DecidableEq α] [Monoid M] [Fintype M]

/-- An observed factor is strictly shorter than the sample norm. -/
theorem observed_length_succ_le_norm
    {K : Finset (Word α)} {x p q : Word α}
    (h : Observed K x p q) :
    x.length + 1 ≤ reconstructionSampleNorm K := by
  have hw := reconstructionSampleWord_encoding_le_norm K h.2
  simp only [List.length_append] at hw
  omega

theorem observedSubstring_length_le_norm
    {K : Finset (Word α)} (A : ObservedSubstringNonterminal K) :
    A.1.length ≤ reconstructionSampleNorm K := by
  obtain ⟨p, q, h⟩ := A.2
  have := observed_length_succ_le_norm h
  omega

/-- Literal length of a (B) rule `A → B C`: three factor strings plus one
separator per symbol. -/
def v116BinaryLiteralLength (K : Finset (Word α))
    (e : V116BinaryEntry K) : Nat :=
  e.1.1.length + e.2.1.1.length + e.2.2.1.length + 3

/-- Literal length of a (U) rule `x → y`. -/
def v116UnaryLiteralLength (e : Word α × Word α) : Nat :=
  e.1.length + e.2.length + 2

/-- Literal length of an (L) rule `A → a`. -/
def v116LexicalLiteralLength (K : Finset (Word α))
    (e : ObservedSubstringNonterminal K × α) : Nat :=
  e.1.1.length + 2

/-- Literal length of an (S) rule `S₀ → A`. -/
def v116StartLiteralLength (K : Finset (Word α))
    (A : ObservedSubstringNonterminal K) : Nat :=
  A.1.length + 1

/-- Total literal length of all rules of the actual v116 grammar `B_h(K)`. -/
noncomputable def v116LiteralOutputLength
    (H : FixedFiniteMonoidHom α M) (K : Finset (Word α)) : Nat :=
  (∑ e ∈ v116BinaryRuleTable K, v116BinaryLiteralLength K e) +
  (∑ e ∈ v116UnaryRuleTable H K, v116UnaryLiteralLength e) +
  (∑ e ∈ v116LexicalRuleTable K, v116LexicalLiteralLength K e) +
  (∑ A ∈ v116StartRuleTable K, v116StartLiteralLength K A) +
  (v116EpsilonStartTable K).card

theorem v116BinaryLiteral_sum_le
    (K : Finset (Word α)) :
    (∑ e ∈ v116BinaryRuleTable K, v116BinaryLiteralLength K e) ≤
      (reconstructionSampleNorm K) ^ 3 *
        (3 * (reconstructionSampleNorm K + 1)) := by
  set n := reconstructionSampleNorm K with hn
  have hsum := Finset.sum_le_card_nsmul (v116BinaryRuleTable K)
    (v116BinaryLiteralLength K) (3 * (n + 1)) (by
      intro e _
      have h1 := observedSubstring_length_le_norm e.1
      have h2 := observedSubstring_length_le_norm e.2.1
      have h3 := observedSubstring_length_le_norm e.2.2
      unfold v116BinaryLiteralLength
      omega)
  rw [smul_eq_mul] at hsum
  exact hsum.trans (Nat.mul_le_mul_right _ (v116BinaryRuleTable_card_le_cube K))

theorem v116UnaryLiteral_sum_le
    (H : FixedFiniteMonoidHom α M) (K : Finset (Word α)) :
    (∑ e ∈ v116UnaryRuleTable H K, v116UnaryLiteralLength e) ≤
      (reconstructionSampleNorm K) ^ 3 *
        (2 * (reconstructionSampleNorm K + 1)) := by
  set n := reconstructionSampleNorm K with hn
  have hsum := Finset.sum_le_card_nsmul (v116UnaryRuleTable H K)
    v116UnaryLiteralLength (2 * (n + 1)) (by
      intro e he
      have hrel := v116UnaryRuleTable_sound H K (x := e.1) (y := e.2)
        (by simpa using he)
      obtain ⟨_, p, q, hx, hy⟩ := hrel
      have h1 := observed_length_succ_le_norm hx
      have h2 := observed_length_succ_le_norm hy
      unfold v116UnaryLiteralLength
      omega)
  rw [smul_eq_mul] at hsum
  exact hsum.trans (Nat.mul_le_mul_right _ (v116UnaryRuleTable_card_le_cube H K))

theorem v116LexicalLiteral_sum_le
    (K : Finset (Word α)) :
    (∑ e ∈ v116LexicalRuleTable K, v116LexicalLiteralLength K e) ≤
      ((reconstructionSampleNorm K) ^ 2 * Fintype.card α) *
        (reconstructionSampleNorm K + 2) := by
  classical
  set n := reconstructionSampleNorm K with hn
  have hsum := Finset.sum_le_card_nsmul (v116LexicalRuleTable K)
    (v116LexicalLiteralLength K) (n + 2) (by
      intro e _
      have h1 := observedSubstring_length_le_norm e.1
      unfold v116LexicalLiteralLength
      omega)
  rw [smul_eq_mul] at hsum
  have hcard : (v116LexicalRuleTable K).card ≤ n ^ 2 * Fintype.card α := by
    calc (v116LexicalRuleTable K).card
        ≤ (Finset.univ : Finset (ObservedSubstringNonterminal K × α)).card := by
          unfold v116LexicalRuleTable
          exact Finset.card_filter_le _ _
      _ = Fintype.card (ObservedSubstringNonterminal K) * Fintype.card α := by
          rw [Finset.card_univ, Fintype.card_prod]
      _ ≤ n ^ 2 * Fintype.card α :=
          Nat.mul_le_mul_right _ (observedSubstring_card_le_sq K)
  exact hsum.trans (Nat.mul_le_mul_right _ hcard)

theorem v116StartLiteral_sum_le
    (K : Finset (Word α)) :
    (∑ A ∈ v116StartRuleTable K, v116StartLiteralLength K A) ≤
      (reconstructionSampleNorm K) ^ 2 *
        (reconstructionSampleNorm K + 1) := by
  classical
  set n := reconstructionSampleNorm K with hn
  have hsum := Finset.sum_le_card_nsmul (v116StartRuleTable K)
    (v116StartLiteralLength K) (n + 1) (by
      intro A _
      have h1 := observedSubstring_length_le_norm A
      unfold v116StartLiteralLength
      omega)
  rw [smul_eq_mul] at hsum
  have hcard : (v116StartRuleTable K).card ≤ n ^ 2 := by
    calc (v116StartRuleTable K).card
        ≤ (Finset.univ : Finset (ObservedSubstringNonterminal K)).card := by
          unfold v116StartRuleTable
          exact Finset.card_filter_le _ _
      _ = Fintype.card (ObservedSubstringNonterminal K) := Finset.card_univ
      _ ≤ n ^ 2 := observedSubstring_card_le_sq K
  exact hsum.trans (Nat.mul_le_mul_right _ hcard)

theorem v116EpsilonStartTable_card_le_one
    (K : Finset (Word α)) :
    (v116EpsilonStartTable K).card ≤ 1 := by
  calc (v116EpsilonStartTable K).card ≤ (Finset.univ : Finset Unit).card :=
        Finset.card_le_univ _
    _ = 1 := by simp

/-- **Total literal output of the actual v116 grammar is quartic.** -/
theorem v116LiteralOutputLength_le_quartic
    (H : FixedFiniteMonoidHom α M) (K : Finset (Word α)) :
    v116LiteralOutputLength H K ≤
      (2 * Fintype.card α + 7) * (reconstructionSampleNorm K + 1) ^ 4 := by
  set n := reconstructionSampleNorm K with hn
  have hB := v116BinaryLiteral_sum_le K
  have hU := v116UnaryLiteral_sum_le H K
  have hL := v116LexicalLiteral_sum_le K
  have hS := v116StartLiteral_sum_le K
  have hE := v116EpsilonStartTable_card_le_one K
  rw [← hn] at hB hU hL hS
  -- monomial dominations in N = n + 1
  have hn1 : n ≤ n + 1 := Nat.le_succ n
  have p3 : n ^ 3 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_left hn1 3
  have p2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left hn1 2
  have q1 : n ^ 3 * (3 * (n + 1)) ≤ 3 * (n + 1) ^ 4 := by
    calc n ^ 3 * (3 * (n + 1)) ≤ (n + 1) ^ 3 * (3 * (n + 1)) :=
          Nat.mul_le_mul_right _ p3
      _ = 3 * (n + 1) ^ 4 := by ring
  have q2 : n ^ 3 * (2 * (n + 1)) ≤ 2 * (n + 1) ^ 4 := by
    calc n ^ 3 * (2 * (n + 1)) ≤ (n + 1) ^ 3 * (2 * (n + 1)) :=
          Nat.mul_le_mul_right _ p3
      _ = 2 * (n + 1) ^ 4 := by ring
  have q3 : (n ^ 2 * Fintype.card α) * (n + 2) ≤ (2 * Fintype.card α) * (n + 1) ^ 4 := by
    have h1 : n + 2 ≤ 2 * (n + 1) := by omega
    have h2 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num)
    calc (n ^ 2 * Fintype.card α) * (n + 2)
          ≤ ((n + 1) ^ 2 * Fintype.card α) * (2 * (n + 1)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ p2) h1
      _ = (2 * Fintype.card α) * (n + 1) ^ 3 := by ring
      _ ≤ (2 * Fintype.card α) * (n + 1) ^ 4 := Nat.mul_le_mul_left _ h2
  have q4 : n ^ 2 * (n + 1) ≤ (n + 1) ^ 4 := by
    have h2 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 :=
      Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num)
    calc n ^ 2 * (n + 1) ≤ (n + 1) ^ 2 * (n + 1) := Nat.mul_le_mul_right _ p2
      _ = (n + 1) ^ 3 := by ring
      _ ≤ (n + 1) ^ 4 := h2
  have q5 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hsplit : (2 * Fintype.card α + 7) * (n + 1) ^ 4 =
      3 * (n + 1) ^ 4 + 2 * (n + 1) ^ 4 +
        (2 * Fintype.card α) * (n + 1) ^ 4 +
        (n + 1) ^ 4 + (n + 1) ^ 4 := by ring
  unfold v116LiteralOutputLength
  omega

/-- Scan every enumerated candidate once (verified cubic count) and write
every actual rule literally: the combined budget is quartic. -/
noncomputable def v116ScanAndWriteBudget
    (H : FixedFiniteMonoidHom α M) (K : Finset (Word α)) : Nat :=
  substringV116CandidateCount H K + v116LiteralOutputLength H K

theorem v116ScanAndWriteBudget_le_quartic
    (H : FixedFiniteMonoidHom α M) (K : Finset (Word α)) :
    v116ScanAndWriteBudget H K ≤
      (2 * Fintype.card α + 11) * (reconstructionSampleNorm K + 1) ^ 4 := by
  set n := reconstructionSampleNorm K with hn
  have hC := substringV116CandidateCount_le_cubic H K
  have hW := v116LiteralOutputLength_le_quartic H K
  rw [← hn] at hC hW
  have h34 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 :=
    Nat.pow_le_pow_right (Nat.succ_pos n) (by norm_num)
  have hsplit : (2 * Fintype.card α + 11) * (n + 1) ^ 4 =
      4 * (n + 1) ^ 4 + (2 * Fintype.card α + 7) * (n + 1) ^ 4 := by ring
  unfold v116ScanAndWriteBudget
  omega

end V135LiteralOutputSize

end TCS1
end LeanCfgProject
