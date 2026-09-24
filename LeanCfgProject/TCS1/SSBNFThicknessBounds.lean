import LeanCfgProject.TCS1.ReducednessWitnessChoices

/-!
# TCS #1: quantitative kernel for the fixed-window / SSBNF bounds

This module formalizes the arithmetic layer used in Section 7 and in the
appendix proof of the polynomial thickness-preserving SSBNF normalization.

It does **not** claim to formalize the grammar transformations themselves.
Instead it records and checks the quantitative implications once the
combinatorial normalization lemmas provide their hypotheses.

The two manuscript formulas represented literally here are

  tau_B <= c1 * n * (tau_R + 1)

and, for a nullable symbol with a nonempty yield,

  minNonempty <= 1 + |V_B| * tau_B,

together with the fixed-window bound

  B_{k,l}(G) = tau_G                         if r = 0,
               r + (2r-1) N tau_G           if r > 0,

where r = k+l.
-/

namespace LeanCfgProject
namespace TCS1

section SSBNFThicknessBounds

/-- The manuscript's harmless positive envelope for target thickness. -/
def thicknessBar (τ : Nat) : Nat :=
  τ + 1

/-- Arithmetic form of the binarized-grammar thickness estimate. -/
def binarizedThicknessEnvelope
    (c₁ n τR : Nat) : Nat :=
  c₁ * n * thicknessBar τR

/--
Arithmetic form of the shortest-nonempty-yield estimate obtained from a
root-to-terminal-leaf path.
-/
def nullableNonemptyEnvelope
    (vB τB : Nat) : Nat :=
  1 + vB * τB

/--
A single polynomial envelope after substituting
  |V_B| <= cV*n
and
  tau_B <= c1*n*(tau_R+1)
into 1+|V_B|*tau_B.
-/
def ssbnfThicknessEnvelope
    (cV c₁ n τR : Nat) : Nat :=
  1 + (cV * c₁) * n^2 * thicknessBar τR

/--
The arithmetic substitution used in the appendix:
linear control of |V_B| and of tau_B implies a quadratic-in-n thickness
envelope for shortest nonempty yields.
-/
theorem nullableNonemptyEnvelope_le_ssbnfThicknessEnvelope
    {cV c₁ n τR vB τB : Nat}
    (hV : vB ≤ cV * n)
    (hτ : τB ≤ binarizedThicknessEnvelope c₁ n τR) :
    nullableNonemptyEnvelope vB τB ≤
      ssbnfThicknessEnvelope cV c₁ n τR := by
  have hmul :
      vB * τB ≤
        (cV * n) * (c₁ * n * thicknessBar τR) :=
    Nat.mul_le_mul hV hτ
  unfold nullableNonemptyEnvelope ssbnfThicknessEnvelope
  unfold binarizedThicknessEnvelope at hmul
  calc
    1 + vB * τB
        ≤ 1 + (cV * n) * (c₁ * n * thicknessBar τR) :=
      Nat.add_le_add_left hmul 1
    _ = 1 + (cV * c₁) * n^2 * thicknessBar τR := by
      ring

/--
Unit elimination and trimming preserve the numerical thickness estimate if
they do not increase any surviving nonterminal's shortest terminal yield.
-/
theorem thickness_bound_transitive
    {τFinal τIntermediate bound : Nat}
    (hFinal : τFinal ≤ τIntermediate)
    (hIntermediate : τIntermediate ≤ bound) :
    τFinal ≤ bound :=
  le_trans hFinal hIntermediate

/--
Exact B_{k,l}(G) formula from Section 7, parameterized by r=k+l.
-/
def fixedWindowTypedYieldBound
    (r N τG : Nat) : Nat :=
  if r = 0 then
    τG
  else
    r + (2 * r - 1) * N * τG

/-- The (0,0) endpoint is exactly tau_G, not the positive-window formula. -/
@[simp] theorem fixedWindowTypedYieldBound_zero
    (N τG : Nat) :
    fixedWindowTypedYieldBound 0 N τG = τG := by
  simp [fixedWindowTypedYieldBound]

/-- For every nonzero window sum, the displayed positive-window formula is used. -/
theorem fixedWindowTypedYieldBound_of_pos
    {r N τG : Nat}
    (hr : 0 < r) :
    fixedWindowTypedYieldBound r N τG =
      r + (2 * r - 1) * N * τG := by
  simp [fixedWindowTypedYieldBound, Nat.ne_of_gt hr]

/--
Monotonicity in the number of underlying non-start nonterminals, for a fixed
positive window and fixed target thickness.
-/
theorem fixedWindowTypedYieldBound_mono_N
    {r N₁ N₂ τG : Nat}
    (hN : N₁ ≤ N₂) :
    fixedWindowTypedYieldBound r N₁ τG ≤
      fixedWindowTypedYieldBound r N₂ τG := by
  by_cases hr : r = 0
  · subst r
    simp
  · simp only [fixedWindowTypedYieldBound, if_neg hr]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right τG
        (Nat.mul_le_mul_left (2 * r - 1) hN))
      r

/-- Monotonicity in grammar thickness for fixed r and N. -/
theorem fixedWindowTypedYieldBound_mono_thickness
    {r N τ₁ τ₂ : Nat}
    (hτ : τ₁ ≤ τ₂) :
    fixedWindowTypedYieldBound r N τ₁ ≤
      fixedWindowTypedYieldBound r N τ₂ := by
  by_cases hr : r = 0
  · subst r
    simpa using hτ
  · simp only [fixedWindowTypedYieldBound, if_neg hr]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_left ((2 * r - 1) * N) hτ)
      r

/--
Common witness-length envelope from Lemma "bounded fixed-window contexts and
witnesses": (N_t+2) B + 1.
-/
def fixedWindowWitnessLengthEnvelope
    (Nt r N τG : Nat) : Nat :=
  (Nt + 2) * fixedWindowTypedYieldBound r N τG + 1

/-- The witness-length envelope at the (0,0) endpoint. -/
@[simp] theorem fixedWindowWitnessLengthEnvelope_zero
    (Nt N τG : Nat) :
    fixedWindowWitnessLengthEnvelope Nt 0 N τG =
      (Nt + 2) * τG + 1 := by
  simp [fixedWindowWitnessLengthEnvelope]

/--
If both the typed-nonterminal count and the typed-yield bound are enlarged,
the common witness-length envelope can only increase.
-/
theorem witnessLengthEnvelope_mono
    {Nt₁ Nt₂ B₁ B₂ : Nat}
    (hNt : Nt₁ ≤ Nt₂)
    (hB : B₁ ≤ B₂) :
    (Nt₁ + 2) * B₁ + 1 ≤
      (Nt₂ + 2) * B₂ + 1 := by
  have hNt' : Nt₁ + 2 ≤ Nt₂ + 2 :=
    Nat.add_le_add_right hNt 2
  have hmul :
      (Nt₁ + 2) * B₁ ≤ (Nt₂ + 2) * B₂ :=
    Nat.mul_le_mul hNt' hB
  exact Nat.add_le_add_right hmul 1

/--
Composition lemma used when Section 7 transfers an SSBNF witness bound back
to an arbitrary reduced CFG representation.
-/
theorem fixedWindowWitnessLength_transfer
    {Nt Nt' r N N' τG τG' : Nat}
    (hNt : Nt ≤ Nt')
    (hN : N ≤ N')
    (hτ : τG ≤ τG') :
    fixedWindowWitnessLengthEnvelope Nt r N τG ≤
      fixedWindowWitnessLengthEnvelope Nt' r N' τG' := by
  unfold fixedWindowWitnessLengthEnvelope
  apply witnessLengthEnvelope_mono hNt
  exact le_trans
    (fixedWindowTypedYieldBound_mono_N
      (r := r) (τG := τG) hN)
    (fixedWindowTypedYieldBound_mono_thickness
      (r := r) (N := N') hτ)

end SSBNFThicknessBounds

end TCS1
end LeanCfgProject
