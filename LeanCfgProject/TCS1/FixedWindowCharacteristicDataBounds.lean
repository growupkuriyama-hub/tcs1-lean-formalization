import LeanCfgProject.TCS1.SSBNFThicknessBounds

/-!
# TCS #1: fixed-window characteristic-data size bounds

This module formalizes the counting layer of the fixed-window theorem.

For a fixed window monoid of size m, the reduced yield-typed refinement has

* at most N*m non-start typed nonterminals;
* at most t typed terminal rules;
* at most b*m^2 typed binary rules.

The canonical witness set has at most one anchor per typed nonterminal, one
witness per typed terminal/binary rule, and possibly epsilon. If every
witness has length at most L, then the paper's sample norm

  ||K|| = sum_{w in K} (|w| + 1)

is at most (# witnesses) * (L + 1).

Combining this with the fixed-window witness-length envelope gives an explicit
arithmetic envelope for the polynomial thick-data theorem. The final theorem
composes this envelope with arbitrary upper bounds supplied by the SSBNF
normalization proposition; this is the arithmetic core of the fixed-window
complexity-transfer corollary.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section FixedWindowCharacteristicDataBounds

/-- Bound on the number of non-start typed nonterminals. -/
def typedNonterminalCountEnvelope
    (N m : Nat) : Nat :=
  N * m

/-- Bound on the number of typed terminal/binary rules. -/
def typedRuleCountEnvelope
    (t b m : Nat) : Nat :=
  t + b * m^2

/--
One anchor per typed nonterminal, one witness per typed rule, plus a possible
epsilon witness.
-/
def witnessCountEnvelope
    (N t b m : Nat) : Nat :=
  typedNonterminalCountEnvelope N m +
    typedRuleCountEnvelope t b m + 1

/--
If a finite sample has at most W words and every word has length at most L,
then its encoded norm is at most W*(L+1).
-/
theorem sampleNorm_le_of_card_and_length
    {α : Type u}
    [DecidableEq α]
    (K : Finset (List α))
    (W L : Nat)
    (hcard : K.card ≤ W)
    (hlen : ∀ w ∈ K, w.length ≤ L) :
    (∑ w ∈ K, (w.length + 1)) ≤ W * (L + 1) := by
  have hEach :
      ∀ w ∈ K, w.length + 1 ≤ L + 1 := by
    intro w hw
    exact Nat.add_le_add_right (hlen w hw) 1
  calc
    (∑ w ∈ K, (w.length + 1))
      ≤ ∑ _w ∈ K, (L + 1) := by
        apply Finset.sum_le_sum
        intro w hw
        exact hEach w hw
    _ = K.card * (L + 1) := by
        simp
    _ ≤ W * (L + 1) :=
      Nat.mul_le_mul_right (L + 1) hcard

/--
Explicit common envelope for the encoded characteristic-data size of one
fixed-window typed refinement.
-/
def fixedWindowCharacteristicEnvelope
    (m r N t b τG : Nat) : Nat :=
  witnessCountEnvelope N t b m *
    (fixedWindowWitnessLengthEnvelope
      (typedNonterminalCountEnvelope N m) r N τG + 1)

/--
The witness-count estimate from the typed-refinement rule multiplicities.
-/
theorem witnessCount_le_envelope
    {Nt tTyped bTyped N t b m : Nat}
    (hNt : Nt ≤ N * m)
    (ht : tTyped ≤ t)
    (hb : bTyped ≤ b * m^2) :
    Nt + tTyped + bTyped + 1 ≤
      witnessCountEnvelope N t b m := by
  unfold witnessCountEnvelope
  unfold typedNonterminalCountEnvelope typedRuleCountEnvelope
  omega

/--
General encoded-size estimate: combine the witness-count estimate with the
fixed-window length bound.
-/
theorem fixedWindow_sampleNorm_bound
    {α : Type u}
    [DecidableEq α]
    (K : Finset (List α))
    {m r N t b τG Nt tTyped bTyped : Nat}
    (hNt : Nt ≤ N * m)
    (ht : tTyped ≤ t)
    (hb : bTyped ≤ b * m^2)
    (hcard : K.card ≤ Nt + tTyped + bTyped + 1)
    (hlen :
      ∀ w ∈ K,
        w.length ≤ fixedWindowWitnessLengthEnvelope Nt r N τG) :
    (∑ w ∈ K, (w.length + 1)) ≤
      fixedWindowCharacteristicEnvelope m r N t b τG := by
  have hCount :
      K.card ≤ witnessCountEnvelope N t b m :=
    le_trans hcard (witnessCount_le_envelope hNt ht hb)
  have hLenMono :
      fixedWindowWitnessLengthEnvelope Nt r N τG ≤
        fixedWindowWitnessLengthEnvelope
          (typedNonterminalCountEnvelope N m) r N τG := by
    apply fixedWindowWitnessLength_transfer
    · simpa [typedNonterminalCountEnvelope] using hNt
    · exact le_rfl
    · exact le_rfl
  apply le_trans
    (sampleNorm_le_of_card_and_length
      K
      (witnessCountEnvelope N t b m)
      (fixedWindowWitnessLengthEnvelope
        (typedNonterminalCountEnvelope N m) r N τG)
      hCount
      (by
        intro w hw
        exact le_trans (hlen w hw) hLenMono))
  rfl

/--
A coarser paper-facing envelope using only a single grammar-size bound g for
N, the number of terminal rules, and the number of binary rules.
-/
def fixedWindowGrammarSizeEnvelope
    (m r g τG : Nat) : Nat :=
  fixedWindowCharacteristicEnvelope m r g g g τG

/--
Replacing N,t,b by a common upper bound g enlarges the characteristic-data
envelope.
-/
theorem fixedWindowCharacteristicEnvelope_le_grammarSize
    {m r N t b g τG : Nat}
    (hN : N ≤ g)
    (ht : t ≤ g)
    (hb : b ≤ g) :
    fixedWindowCharacteristicEnvelope m r N t b τG ≤
      fixedWindowGrammarSizeEnvelope m r g τG := by
  unfold fixedWindowCharacteristicEnvelope fixedWindowGrammarSizeEnvelope
  unfold witnessCountEnvelope typedNonterminalCountEnvelope typedRuleCountEnvelope
  have hNm : N * m ≤ g * m :=
    Nat.mul_le_mul_right m hN
  have hbm2 : b * m^2 ≤ g * m^2 :=
    Nat.mul_le_mul_right (m^2) hb
  have hCount :
      N * m + (t + b * m^2) + 1
        ≤ g * m + (g + g * m^2) + 1 := by
    omega
  have hLen :
      fixedWindowWitnessLengthEnvelope (N * m) r N τG + 1
        ≤ fixedWindowWitnessLengthEnvelope (g * m) r g τG + 1 := by
    apply Nat.add_le_add_right
    exact fixedWindowWitnessLength_transfer hNm hN le_rfl
  exact Nat.mul_le_mul hCount hLen

/--
Monotonicity of the coarse fixed-window data envelope in grammar size and
thickness.
-/
theorem fixedWindowGrammarSizeEnvelope_mono
    {m r g₁ g₂ τ₁ τ₂ : Nat}
    (hg : g₁ ≤ g₂)
    (hτ : τ₁ ≤ τ₂) :
    fixedWindowGrammarSizeEnvelope m r g₁ τ₁ ≤
      fixedWindowGrammarSizeEnvelope m r g₂ τ₂ := by
  unfold fixedWindowGrammarSizeEnvelope fixedWindowCharacteristicEnvelope
  unfold witnessCountEnvelope typedNonterminalCountEnvelope typedRuleCountEnvelope
  have hgm : g₁ * m ≤ g₂ * m :=
    Nat.mul_le_mul_right m hg
  have hgm2 : g₁ * m^2 ≤ g₂ * m^2 :=
    Nat.mul_le_mul_right (m^2) hg
  have hCount :
      g₁ * m + (g₁ + g₁ * m^2) + 1
        ≤ g₂ * m + (g₂ + g₂ * m^2) + 1 := by
    omega
  have hLen :
      fixedWindowWitnessLengthEnvelope (g₁ * m) r g₁ τ₁ + 1
        ≤ fixedWindowWitnessLengthEnvelope (g₂ * m) r g₂ τ₂ + 1 := by
    apply Nat.add_le_add_right
    exact fixedWindowWitnessLength_transfer hgm hg hτ
  exact Nat.mul_le_mul hCount hLen

/--
Arithmetic core of the fixed-window complexity-transfer corollary.

If normalization produces an SSBNF representation of size at most gBound
and thickness at most tauBound, then its fixed-window characteristic data
is bounded by the same explicit envelope evaluated at those two bounds.
-/
theorem fixedWindow_complexity_transfer
    {m r g τG gBound τBound : Nat}
    (hg : g ≤ gBound)
    (hτ : τG ≤ τBound) :
    fixedWindowGrammarSizeEnvelope m r g τG ≤
      fixedWindowGrammarSizeEnvelope m r gBound τBound :=
  fixedWindowGrammarSizeEnvelope_mono hg hτ

/--
The (0,0) slice is included literally: the bound substitutes tau_G for the
typed-yield term rather than using the positive-window expression.
-/
@[simp] theorem fixedWindowGrammarSizeEnvelope_zero
    (m g τG : Nat) :
    fixedWindowGrammarSizeEnvelope m 0 g τG =
      (g * m + (g + g * m^2) + 1) *
        (((g * m + 2) * τG + 1) + 1) := by
  simp [fixedWindowGrammarSizeEnvelope,
    fixedWindowCharacteristicEnvelope,
    witnessCountEnvelope,
    typedNonterminalCountEnvelope,
    typedRuleCountEnvelope,
    fixedWindowWitnessLengthEnvelope]

end FixedWindowCharacteristicDataBounds

end TCS1
end LeanCfgProject
