import LeanCfgProject.TCS1.V135LinearEnvelopeArith
import LeanCfgProject.TCS1.IndexedLinearCharacteristicData
import LeanCfgProject.TCS1.V135ItemIVv116Operator

/-!
# TCS #1 v135: `thm:main` item (v), manuscript-exact form

Manuscript `thm:main` (v):

> for arbitrary fixed `h` and `L ∈ C^lin_h`, the sample in (ii) can be chosen
> polynomial in `|G_*|` for any linear CFG `G_*` representing `L`.
> The polynomials … may depend on the fixed `h` and `Σ`, but not on `G_*`.

The verified `indexedLinear_characteristic_package` (no reducedness, no
nonemptiness assumption) gives exact reconstruction `BatchLanguage H K = L`
from the canonical sample and a symbolic envelope.  This module

* upgrades exact reconstruction to the §2 set-driven characteristic-sample
  property;
* bounds the envelope by `c · (|G_*| + 1)^12`, with `|G_*|` the encoding
  scale `|N| + |P| + Σ_p |rhs p|` (it lists the nonterminals and the
  productions; for an arbitrary, possibly non-reduced grammar this is the
  natural encoding size) and `c` depending only on `|M|` and `|Σ|`;
* gives the same statement for the manuscript's v116 operator.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section V135MainTheoremItemV

variable {α : Type v} [Fintype α] [DecidableEq α]
variable {M : Type q} [Monoid M] [Fintype M]

theorem indexedLinearCharacteristicEnvelope_le_poly (m n : Nat) :
    indexedLinearCharacteristicEnvelope m n ≤ linEnvConst m * (n + 1) ^ 12 := by
  have h := linEnvelope_unfolded_le_poly m n
  unfold indexedLinearCharacteristicEnvelope linearSourceCharacteristicEnvelope
    linearCharacteristicEnvelope witnessCountEnvelope typedNonterminalCountEnvelope
    typedRuleCountEnvelope linearCanonicalWitnessLengthEnvelope
    linearPreparedEncodingEnvelope
  exact h

/-- Constant of `thm:main` (v): depends only on `|M|` and `|Σ|`. -/
def corLinConst (_H : FixedFiniteMonoidHom α M) : Nat :=
  linEnvConst (Fintype.card M) * (Fintype.card α + 1) ^ 12

/-- Per-grammar form of `thm:main` (v). -/
theorem thm_main_item_v_bound (H : FixedFiniteMonoidHom α M)
    {N : Type u} {P : Type w} [Fintype N] [Fintype P]
    (G : IndexedMixedCFG N α P) (hlin : G.IsLinear) (S : N)
    (hsub : FixedHSubstitutable H (MixedNonterminalLanguage G.toMixedRules S)) :
    ∃ K : Finset (Word α),
      IsSetDrivenCharacteristicSample (BatchLanguage H)
        (MixedNonterminalLanguage G.toMixedRules S) K ∧
      (∑ x ∈ K, (x.length + 1)) ≤ corLinConst H * (G.encodingScale + 1) ^ 12 := by
  have hEq := leastClosedLanguage_eq_mixedNonterminalLanguage G.toMixedRules S
  have hsub' : FixedHSubstitutable H (LeastClosedLanguage G.toMixedRules S) := by
    rw [hEq]; exact hsub
  obtain ⟨hK, hnorm⟩ := indexedLinear_characteristic_package H G hlin S hsub'
  refine ⟨_, isSetDrivenCharacteristicSample_of_batch_eq H _ _ hsub (hK.trans hEq), ?_⟩
  have hscale : G.linearNormalizationSourceScale + 1 ≤
      (Fintype.card α + 1) * (G.encodingScale + 1) := by
    unfold IndexedMixedCFG.linearNormalizationSourceScale
    nlinarith [Nat.zero_le (Fintype.card α * G.encodingScale)]
  calc (∑ x ∈ indexedLinearCanonicalSample H G hlin S, (x.length + 1))
      ≤ indexedLinearCharacteristicEnvelope (Fintype.card M)
          G.linearNormalizationSourceScale := hnorm
    _ ≤ linEnvConst (Fintype.card M) * (G.linearNormalizationSourceScale + 1) ^ 12 :=
        indexedLinearCharacteristicEnvelope_le_poly _ _
    _ ≤ linEnvConst (Fintype.card M) *
          ((Fintype.card α + 1) * (G.encodingScale + 1)) ^ 12 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hscale 12)
    _ = corLinConst H * (G.encodingScale + 1) ^ 12 := by
        unfold corLinConst; ring

/--
**`thm:main` (v), manuscript-exact form.**  For a fixed finite-monoid typing
`H` there are constants `c, d` (depending only on `|M|` and `|Σ|`) such that
for **every** linear finite indexed CFG `G_*` with start `S` whose language
`L` is `H`-substitutable, `L` has a characteristic sample for `B_h` (full
set-driven sense, original `H`) of encoded size `≤ c · (|G_*| + 1)^d`.
No reducedness or nonemptiness is assumed.
-/
theorem thm_main_item_v (H : FixedFiniteMonoidHom α M) :
    ∃ c d : Nat, c = corLinConst H ∧ d = 12 ∧
      ∀ {N : Type u} {P : Type w} [Fintype N] [Fintype P]
        (G : IndexedMixedCFG N α P), G.IsLinear → ∀ S : N,
        FixedHSubstitutable H (MixedNonterminalLanguage G.toMixedRules S) →
        ∃ K : Finset (Word α),
          IsSetDrivenCharacteristicSample (BatchLanguage H)
            (MixedNonterminalLanguage G.toMixedRules S) K ∧
          (∑ x ∈ K, (x.length + 1)) ≤ c * (G.encodingScale + 1) ^ d := by
  refine ⟨corLinConst H, 12, rfl, rfl, ?_⟩
  intro N P _ _ G hlin S hsub
  exact thm_main_item_v_bound H G hlin S hsub

/-- `thm:main` (v) for the manuscript's v116 operator. -/
theorem thm_main_item_v_bound_v116 (H : FixedFiniteMonoidHom α M)
    {N : Type u} {P : Type w} [Fintype N] [Fintype P]
    (G : IndexedMixedCFG N α P) (hlin : G.IsLinear) (S : N)
    (hsub : FixedHSubstitutable H (MixedNonterminalLanguage G.toMixedRules S)) :
    ∃ K : Finset (Word α),
      IsSetDrivenCharacteristicSample (v116TabulatedBatchLanguage H)
        (MixedNonterminalLanguage G.toMixedRules S) K ∧
      (∑ x ∈ K, (x.length + 1)) ≤ corLinConst H * (G.encodingScale + 1) ^ 12 := by
  obtain ⟨K, hK, hnorm⟩ := thm_main_item_v_bound H G hlin S hsub
  exact ⟨K, (isSetDrivenCharacteristicSample_v116_iff H _ K).2 hK, hnorm⟩

end V135MainTheoremItemV

end TCS1
end LeanCfgProject
