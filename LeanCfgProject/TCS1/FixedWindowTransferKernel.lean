import LeanCfgProject.TCS1.FixedWindowCharacteristicDataBounds
import LeanCfgProject.TCS1.SSBNFNormalizationSemanticKernel
import LeanCfgProject.TCS1.SSBNFNormalizationCombinatorics

/-!
# TCS #1: fixed-window complexity-transfer kernel

This module composes the pieces already verified for Section 7:

* typed nonterminal/rule counting for a fixed window monoid;
* the common canonical-witness length bound;
* the paper's encoded sample norm;
* polynomial size/thickness upper bounds supplied by SSBNF normalization.

The result is a theorem shaped like the quantitative part of the
fixed-window complexity-transfer corollary. Grammar normalization semantics
and exact reconstruction are proved in separate modules; here we verify the
numerical composition without hiding any dependence on the fixed monoid size
or on the (0,0) endpoint.
-/

namespace LeanCfgProject
namespace TCS1

section FixedWindowTransferKernel

/--
One-stop encoded characteristic-data estimate for a normalized SSBNF grammar.

g is a common upper bound on the normalized grammar's non-start
nonterminals, terminal rules, and binary rules. gBound and tauBound are
the bounds supplied by normalization from the original representation.
-/
theorem fixedWindow_normalized_sample_transfer
    {α : Type}
    [DecidableEq α]
    (K : Finset (List α))
    {m r N t b τG Nt tTyped bTyped g gBound τBound : Nat}
    (hNt : Nt ≤ N * m)
    (htTyped : tTyped ≤ t)
    (hbTyped : bTyped ≤ b * m^2)
    (hcard : K.card ≤ Nt + tTyped + bTyped + 1)
    (hlen :
      ∀ w ∈ K,
        w.length ≤ fixedWindowWitnessLengthEnvelope Nt r N τG)
    (hN : N ≤ g)
    (ht : t ≤ g)
    (hb : b ≤ g)
    (hg : g ≤ gBound)
    (hτ : τG ≤ τBound) :
    (∑ w ∈ K, (w.length + 1)) ≤
      fixedWindowGrammarSizeEnvelope m r gBound τBound := by
  have h0 :
      (∑ w ∈ K, (w.length + 1)) ≤
        fixedWindowCharacteristicEnvelope m r N t b τG :=
    fixedWindow_sampleNorm_bound
      K hNt htTyped hbTyped hcard hlen
  have h1 :
      fixedWindowCharacteristicEnvelope m r N t b τG ≤
        fixedWindowGrammarSizeEnvelope m r g τG :=
    fixedWindowCharacteristicEnvelope_le_grammarSize hN ht hb
  have h2 :
      fixedWindowGrammarSizeEnvelope m r g τG ≤
        fixedWindowGrammarSizeEnvelope m r gBound τBound :=
    fixedWindow_complexity_transfer hg hτ
  exact le_trans h0 (le_trans h1 h2)

/--
Substitute the explicit quadratic thickness envelope from the appendix.
-/
theorem fixedWindow_transfer_with_ssbnf_thickness
    {α : Type}
    [DecidableEq α]
    (K : Finset (List α))
    {m r N t b τG Nt tTyped bTyped g gBound : Nat}
    (cV c₁ n τR : Nat)
    (hNt : Nt ≤ N * m)
    (htTyped : tTyped ≤ t)
    (hbTyped : bTyped ≤ b * m^2)
    (hcard : K.card ≤ Nt + tTyped + bTyped + 1)
    (hlen :
      ∀ w ∈ K,
        w.length ≤ fixedWindowWitnessLengthEnvelope Nt r N τG)
    (hN : N ≤ g)
    (ht : t ≤ g)
    (hb : b ≤ g)
    (hg : g ≤ gBound)
    (hτ :
      τG ≤ ssbnfThicknessEnvelope cV c₁ n τR) :
    (∑ w ∈ K, (w.length + 1)) ≤
      fixedWindowGrammarSizeEnvelope
        m r gBound
        (ssbnfThicknessEnvelope cV c₁ n τR) := by
  exact fixedWindow_normalized_sample_transfer
    K
    hNt htTyped hbTyped hcard hlen
    hN ht hb hg hτ

/--
The (0,0) slice follows from exactly the same transfer theorem and reduces to
the thickness-only typed-yield bound.
-/
theorem zeroWindow_transfer_with_ssbnf_thickness
    {α : Type}
    [DecidableEq α]
    (K : Finset (List α))
    {m N t b τG Nt tTyped bTyped g gBound : Nat}
    (cV c₁ n τR : Nat)
    (hNt : Nt ≤ N * m)
    (htTyped : tTyped ≤ t)
    (hbTyped : bTyped ≤ b * m^2)
    (hcard : K.card ≤ Nt + tTyped + bTyped + 1)
    (hlen :
      ∀ w ∈ K,
        w.length ≤ fixedWindowWitnessLengthEnvelope Nt 0 N τG)
    (hN : N ≤ g)
    (ht : t ≤ g)
    (hb : b ≤ g)
    (hg : g ≤ gBound)
    (hτ :
      τG ≤ ssbnfThicknessEnvelope cV c₁ n τR) :
    (∑ w ∈ K, (w.length + 1)) ≤
      fixedWindowGrammarSizeEnvelope
        m 0 gBound
        (ssbnfThicknessEnvelope cV c₁ n τR) := by
  exact fixedWindow_transfer_with_ssbnf_thickness
    K cV c₁ n τR
    hNt htTyped hbTyped hcard hlen
    hN ht hb hg hτ

/--
The binary-first normalization counting facts yield an explicit quadratic
raw-rule envelope, matching the size side of the appendix proof.
-/
theorem ssbnf_raw_rule_and_thickness_envelopes
    {v p t cV cP cT c₁ n τR τB : Nat}
    (hv : v ≤ cV * n)
    (hp : p ≤ cP * n)
    (ht : t ≤ cT * n)
    (hτ : τB ≤ binarizedThicknessEnvelope c₁ n τR) :
    v * (t + 3 * p)
        ≤ (cV * (cT + 3 * cP)) * n^2
    ∧
    nullableNonemptyEnvelope v τB
        ≤ ssbnfThicknessEnvelope cV c₁ n τR := by
  constructor
  · exact normalization_rule_count_quadratic hv hp ht
  · exact nullableNonemptyEnvelope_le_ssbnfThicknessEnvelope hv hτ

end FixedWindowTransferKernel

end TCS1
end LeanCfgProject
