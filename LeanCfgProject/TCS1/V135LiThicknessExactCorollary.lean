import LeanCfgProject.TCS1.V128IndexedLocallyTrivialCharacteristicData
import LeanCfgProject.TCS1.BatchLanguageMonotonicity
import LeanCfgProject.TCS1.SetDrivenCharacteristicObstruction

/-!
# TCS #1 v135: manuscript-facing form of `cor:li-thickness`

Manuscript (`Papers/01_fixed-h-cfg/main.tex`, v135, sha256 `e8590799…`):

> **Corollary (cor:li-thickness).** Fix `h : Σ* → M` and suppose that
> `h(Σ⁺)` is locally trivial.  Then every nonempty `L ∈ C_h` represented by
> a reduced CFG `G_*` has characteristic data for `B_h` whose encoded size is
> polynomial in `|G_*|` and `τ_{G_*}`.

with the conventions of Section 2:

* a *characteristic sample* of `L` for `B` is a finite `C ⊆ L` such that
  `C ⊆ K ⊆ L` implies `L(B(K)) = L` for every finite `K`
  (here `IsSetDrivenCharacteristicSample (BatchLanguage H) L C`);
* `‖K‖ = ∑_{w∈K} (|w|+1)`;
* `τ_G = max_A min {|w| : A ⇒* w}` (ordinary thickness, `λ` allowed);
* `|G|` is a reasonable encoding, polynomially equivalent to the usual
  symbol count of the productions (here `symbolCount = ∑_p (1 + |rhs p|)`).

This file proves, without new hypotheses beyond those of the corollary:

1. `leastClosedLanguage_eq_mixedNonterminalLanguage`: the least-fixed-point
   semantics used by the normalization equals the parse-tree language.
2. `IndexedMixedCFG.ordinaryThickness`: the exact max–min ordinary thickness,
   with `IndexedMixedThicknessAtMost G τ_G` and minimality.
3. `normalizationScale_le_symbolCount`: for a reduced grammar the internal
   normalization scale `|N|+|Σ|+|P|+∑|rhs|` is at most `|Σ| + 2·|G| + 1`.
4. `liThicknessEnvelope_le_poly`: the concrete envelope delivered by the
   existing normalization pipeline is dominated by `C · (s+τ+1)^12`.
5. `cor_liThickness_exact`: constants `c, d` depending only on the fixed
   typing `H` (via `|M|`, the explicit window `n = |h(Σ⁺)|+1` and `|Σ|`)
   such that **every** reduced finite indexed CFG `G_*` (over any finite
   nonterminal and production index types) whose language is `h`-substitutable
   has a characteristic sample for `B_h` (in the full set-driven sense) with
   `‖K‖ ≤ c · (|G_*| + τ_{G_*} + 1)^d`.

All the mathematical work (window refinement, SSBNF normalization, witness
sample, characteristic reconstruction with the *original* `H`) is reused from
the already verified modules; this file only discharges the remaining
quantifier/encoding obligations.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

/-! ## 1. Least-closed semantics equals parse-tree semantics -/

section LeastClosedEqDerivations

variable {N : Type u} {α : Type v}

/-- The parse-tree languages form a rule-closed interpretation. -/
theorem mixedNonterminalLanguage_closed
    (R : MixedRules N α) :
    GrammarClosed R (MixedNonterminalLanguage R) := by
  intro A w hw
  exact (mixedDerives_iff_ruleStep (R := R) (A := A) (w := w)).2 hw

/-- The least rule-closed language of a nonterminal is exactly the set of
yields of its successful parse trees. -/
theorem leastClosedLanguage_eq_mixedNonterminalLanguage
    (R : MixedRules N α) (A : N) :
    LeastClosedLanguage R A = MixedNonterminalLanguage R A := by
  ext w
  constructor
  · intro hw
    exact hw _ (mixedNonterminalLanguage_closed R)
  · intro hw
    exact mixedDerives_mem_leastClosed R hw

end LeastClosedEqDerivations

/-! ## 2. Exact ordinary thickness `τ_G = max_A min |w|` -/

section OrdinaryThickness

variable {N : Type u} {α : Type v} {P : Type w}

open Classical in
/-- Length of a shortest terminal yield of `A` (`0` if `A` is unproductive). -/
noncomputable def indexedShortestYield
    (G : IndexedMixedCFG N α P) (A : N) : Nat :=
  if h : ∃ n, ∃ x : List α,
      MixedDerives G.toMixedRules A x ∧ x.length = n then
    Nat.find h
  else 0

/-- A productive nonterminal attains its shortest-yield length. -/
theorem indexedShortestYield_spec
    (G : IndexedMixedCFG N α P) {A : N}
    (hA : IndexedMixedProductive G A) :
    ∃ x : List α,
      MixedDerives G.toMixedRules A x ∧
      x.length = indexedShortestYield G A := by
  classical
  obtain ⟨x, hx⟩ := hA
  have h : ∃ n, ∃ x : List α,
      MixedDerives G.toMixedRules A x ∧ x.length = n :=
    ⟨x.length, x, hx, rfl⟩
  unfold indexedShortestYield
  rw [dif_pos h]
  exact Nat.find_spec h

/-- No yield of `A` is shorter than the shortest-yield length. -/
theorem indexedShortestYield_le
    (G : IndexedMixedCFG N α P) {A : N} {x : List α}
    (hx : MixedDerives G.toMixedRules A x) :
    indexedShortestYield G A ≤ x.length := by
  classical
  have h : ∃ n, ∃ y : List α,
      MixedDerives G.toMixedRules A y ∧ y.length = n :=
    ⟨x.length, x, hx, rfl⟩
  unfold indexedShortestYield
  rw [dif_pos h]
  exact Nat.find_min' h ⟨x, hx, rfl⟩

/-- Ordinary thickness `τ_G := max_A min {|w| : A ⇒* w}`. -/
noncomputable def IndexedMixedCFG.ordinaryThickness
    [Fintype N]
    (G : IndexedMixedCFG N α P) : Nat :=
  Finset.univ.sup (fun A => indexedShortestYield G A)

/-- In a grammar whose nonterminals are all productive, every nonterminal
has a yield of length at most `τ_G`. -/
theorem ordinaryThickness_thicknessAtMost
    [Fintype N]
    (G : IndexedMixedCFG N α P)
    (hprod : ∀ A : N, IndexedMixedProductive G A) :
    IndexedMixedThicknessAtMost G G.ordinaryThickness := by
  intro A
  obtain ⟨x, hx, hlen⟩ := indexedShortestYield_spec G (hprod A)
  refine ⟨x, hx, ?_⟩
  rw [hlen]
  exact Finset.le_sup (f := fun B => indexedShortestYield G B)
    (Finset.mem_univ A)

/-- `τ_G` is the *least* uniform shortest-yield bound. -/
theorem ordinaryThickness_le_of_thicknessAtMost
    [Fintype N]
    (G : IndexedMixedCFG N α P)
    {B : Nat}
    (hB : IndexedMixedThicknessAtMost G B) :
    G.ordinaryThickness ≤ B := by
  unfold IndexedMixedCFG.ordinaryThickness
  apply Finset.sup_le
  intro A _
  obtain ⟨x, hx, hlen⟩ := hB A
  exact le_trans (indexedShortestYield_le G hx) hlen

end OrdinaryThickness

/-! ## 3. The usual symbol count controls the normalization scale -/

section SymbolCount

variable {N : Type u} {α : Type v} {P : Type w}

/-- Usual symbol count `|G| = ∑_p (1 + |rhs p|)` (left side plus right side
of every production). -/
def IndexedMixedCFG.symbolCount
    [Fintype P]
    (G : IndexedMixedCFG N α P) : Nat :=
  ∑ p : P, ((G.rhs p).length + 1)

theorem symbolCount_eq
    [Fintype P]
    (G : IndexedMixedCFG N α P) :
    G.symbolCount = G.totalRhsLength + Fintype.card P := by
  simp [IndexedMixedCFG.symbolCount, IndexedMixedCFG.totalRhsLength,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one]

/-- A reachable nonterminal is the start symbol or occurs in some RHS. -/
theorem indexedMixedReachable_eq_or_mem_rhs
    {G : IndexedMixedCFG N α P} {S B : N}
    (h : IndexedMixedReachable G S B) :
    B = S ∨ ∃ p, Sum.inl B ∈ G.rhs p := by
  cases h with
  | start => exact Or.inl rfl
  | child _ _ hmem => exact Or.inr ⟨_, hmem⟩

/-- If every nonterminal is reachable from `S`, then `|N| ≤ ∑|rhs| + 1`. -/
theorem card_nonterminal_le_of_reachable
    [Fintype N] [Fintype P]
    (G : IndexedMixedCFG N α P) (S : N)
    (hreach : ∀ B : N, IndexedMixedReachable G S B) :
    Fintype.card N ≤ G.totalRhsLength + 1 := by
  classical
  have key : ∀ B : N, B ≠ S →
      ∃ o : ProductionOccurrence G,
        occurrenceSymbol G o = Sum.inl B := by
    intro B hB
    rcases indexedMixedReachable_eq_or_mem_rhs (hreach B) with h | ⟨p, hp⟩
    · exact absurd h hB
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hp
      exact ⟨⟨p, i⟩, hi⟩
  let f : N → Option (ProductionOccurrence G) := fun B =>
    if h : B = S then none else some (Classical.choose (key B h))
  have hf : Function.Injective f := by
    intro B C hBC
    by_cases hB : B = S <;> by_cases hC : C = S
    · rw [hB, hC]
    · simp [f, hB, hC] at hBC
    · simp [f, hB, hC] at hBC
    · simp only [f, dif_neg hB, dif_neg hC, Option.some.injEq] at hBC
      have h1 := Classical.choose_spec (key B hB)
      have h2 := Classical.choose_spec (key C hC)
      rw [hBC] at h1
      rw [h1] at h2
      exact Sum.inl_injective h2
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_option, productionOccurrence_card] using hcard

/-- For a reduced grammar the internal normalization scale
`|N|+|Σ|+|P|+∑|rhs|` is linear in the symbol count, with the fixed `|Σ|`
as additive constant. -/
theorem normalizationScale_le_symbolCount
    [Fintype N] [Fintype α] [Fintype P]
    (G : IndexedMixedCFG N α P) (S : N)
    (hred : IndexedMixedReduced G S) :
    G.normalizationScale ≤
      Fintype.card α + 2 * G.symbolCount + 1 := by
  have hN := card_nonterminal_le_of_reachable G S hred.1
  have hs := symbolCount_eq G
  unfold IndexedMixedCFG.normalizationScale
  omega

end SymbolCount

/-! ## 4. The concrete envelope is a polynomial -/

section EnvelopePolynomial

/-- Constant of the degree-4 (in `Y = X^3`) domination of the envelope. -/
def liEnvelopeConst (m r : Nat) : Nat :=
  (3 * m + 3 + 3 * m ^ 2 + 1) * ((3 * m + 2) * (13 * r + 2) + 2) + 1

/-- Abstract domination: if the SSBNF grammar-size parameter is at most
`3Y` and the SSBNF thickness parameter at most `2Y` (`Y ≥ 1`), the
characteristic-data envelope is at most `C(m,r) · Y^4`. -/
theorem fixedWindowGrammarSizeEnvelope_le_poly
    (m r g t Y : Nat)
    (hY : 1 ≤ Y)
    (hg : g ≤ 3 * Y)
    (ht : t ≤ 2 * Y) :
    1 + fixedWindowGrammarSizeEnvelope m r g t ≤
      liEnvelopeConst m r * Y ^ 4 := by
  have hY2 : Y ≤ Y ^ 2 := by nlinarith
  have hT : fixedWindowTypedYieldBound r g t ≤ (13 * r + 2) * Y ^ 2 := by
    unfold fixedWindowTypedYieldBound
    split_ifs with hr
    · subst hr
      nlinarith
    · have h1 : 2 * r - 1 ≤ 2 * r := Nat.sub_le _ _
      have h2 : (2 * r - 1) * g * t ≤ (2 * r) * (3 * Y) * (2 * Y) :=
        Nat.mul_le_mul (Nat.mul_le_mul h1 hg) ht
      have h3 : r ≤ r * Y ^ 2 := by
        have : 1 ≤ Y ^ 2 := Nat.one_le_pow _ _ hY
        nlinarith
      have h4 : (2 * r) * (3 * Y) * (2 * Y) = 12 * (r * Y ^ 2) := by ring
      have h5 : (13 * r + 2) * Y ^ 2 = 13 * (r * Y ^ 2) + 2 * Y ^ 2 := by ring
      omega
  set T := fixedWindowTypedYieldBound r g t with hTdef
  have hA : g * m + (g + g * m ^ 2) + 1 ≤ (3 * m + 3 + 3 * m ^ 2 + 1) * Y := by
    have a1 : g * m ≤ 3 * Y * m := Nat.mul_le_mul_right m hg
    have a2 : g * m ^ 2 ≤ 3 * Y * m ^ 2 := Nat.mul_le_mul_right (m ^ 2) hg
    have a3 : (3 * m + 3 + 3 * m ^ 2 + 1) * Y =
        3 * Y * m + 3 * Y + 3 * Y * m ^ 2 + Y := by ring
    omega
  have hB : (g * m + 2) * T + 1 + 1 ≤
      ((3 * m + 2) * (13 * r + 2) + 2) * Y ^ 3 := by
    have b0 : g * m + 2 ≤ (3 * m + 2) * Y := by
      have a1 : g * m ≤ 3 * Y * m := Nat.mul_le_mul_right m hg
      have : (3 * m + 2) * Y = 3 * Y * m + 2 * Y := by ring
      omega
    have b1 : (g * m + 2) * T ≤ ((3 * m + 2) * Y) * ((13 * r + 2) * Y ^ 2) :=
      Nat.mul_le_mul b0 hT
    have b2 : ((3 * m + 2) * Y) * ((13 * r + 2) * Y ^ 2) =
        (3 * m + 2) * (13 * r + 2) * Y ^ 3 := by ring
    have b3 : 1 ≤ Y ^ 3 := Nat.one_le_pow _ _ hY
    have b4 : ((3 * m + 2) * (13 * r + 2) + 2) * Y ^ 3 =
        (3 * m + 2) * (13 * r + 2) * Y ^ 3 + 2 * Y ^ 3 := by ring
    omega
  have hprod :
      (g * m + (g + g * m ^ 2) + 1) * ((g * m + 2) * T + 1 + 1) ≤
        ((3 * m + 3 + 3 * m ^ 2 + 1) * Y) *
          (((3 * m + 2) * (13 * r + 2) + 2) * Y ^ 3) :=
    Nat.mul_le_mul hA hB
  have hEq : ((3 * m + 3 + 3 * m ^ 2 + 1) * Y) *
          (((3 * m + 2) * (13 * r + 2) + 2) * Y ^ 3) =
        ((3 * m + 3 + 3 * m ^ 2 + 1) *
          ((3 * m + 2) * (13 * r + 2) + 2)) * Y ^ 4 := by ring
  have hY4 : 1 ≤ Y ^ 4 := Nat.one_le_pow _ _ hY
  have hC : liEnvelopeConst m r * Y ^ 4 =
      ((3 * m + 3 + 3 * m ^ 2 + 1) *
        ((3 * m + 2) * (13 * r + 2) + 2)) * Y ^ 4 + Y ^ 4 := by
    unfold liEnvelopeConst; ring
  have hunfold : fixedWindowGrammarSizeEnvelope m r g t =
      (g * m + (g + g * m ^ 2) + 1) * ((g * m + 2) * T + 1 + 1) := by
    simp only [fixedWindowGrammarSizeEnvelope, fixedWindowCharacteristicEnvelope,
      witnessCountEnvelope, typedNonterminalCountEnvelope,
      typedRuleCountEnvelope, fixedWindowWitnessLengthEnvelope, hTdef]
  rw [hunfold]
  omega

/-- The concrete source envelope produced by the verified normalization
pipeline, in the source scale `s` and thickness `τ`, is dominated by
`C(m,r) · (s + τ + 1)^12`. -/
theorem liThicknessEnvelope_le_poly
    (m r s τ : Nat) :
    1 + fixedWindowGrammarSizeEnvelope m r
        (indexedSSBNFGrammarSizeEnvelope s)
        (ssbnfThicknessEnvelope 1 1 s τ) ≤
      liEnvelopeConst m r * (s + τ + 1) ^ 12 := by
  set X := s + τ + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hsX : s ≤ X := by omega
  have hτX : τ + 1 ≤ X := by omega
  have hXX2 : X ≤ X ^ 2 := by nlinarith
  have hX2X3 : X ^ 2 ≤ X ^ 3 := by
    have : X ^ 3 = X ^ 2 * X := by ring
    rw [this]; exact Nat.le_mul_of_pos_right _ hX1
  have hs2 : s * s ≤ X ^ 2 := by
    have := Nat.mul_le_mul hsX hsX
    simpa [pow_two] using this
  have hs3 : s * (s * s) ≤ X ^ 3 := by
    have := Nat.mul_le_mul hsX hs2
    have e : X * X ^ 2 = X ^ 3 := by ring
    omega
  have hg : indexedSSBNFGrammarSizeEnvelope s ≤ 3 * X ^ 3 := by
    unfold indexedSSBNFGrammarSizeEnvelope
    omega
  have ht : ssbnfThicknessEnvelope 1 1 s τ ≤ 2 * X ^ 3 := by
    unfold ssbnfThicknessEnvelope thicknessBar
    have h1 : s ^ 2 * (τ + 1) ≤ X ^ 2 * X := by
      have : s ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hsX 2
      exact Nat.mul_le_mul this hτX
    have h2 : X ^ 2 * X = X ^ 3 := by ring
    have h3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
    have h4 : 1 * 1 * s ^ 2 * (τ + 1) = s ^ 2 * (τ + 1) := by ring
    omega
  have hY : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
  have key := fixedWindowGrammarSizeEnvelope_le_poly m r
    (indexedSSBNFGrammarSizeEnvelope s)
    (ssbnfThicknessEnvelope 1 1 s τ) (X ^ 3) hY hg ht
  have e : (X ^ 3) ^ 4 = X ^ 12 := by ring
  rw [e] at key
  exact key

/-- Monomial domination is preserved under a linear change of the base. -/
theorem pow_base_le_of_le_mul
    {x y a d : Nat} (h : x ≤ a * y) :
    x ^ d ≤ a ^ d * y ^ d := by
  calc x ^ d ≤ (a * y) ^ d := Nat.pow_le_pow_left h d
    _ = a ^ d * y ^ d := by ring

end EnvelopePolynomial

/-! ## 5. The manuscript corollary -/

section CorLiThicknessExact

variable {α : Type v} [Fintype α] [DecidableEq α]
variable {M : Type q} [Monoid M] [Fintype M]

/-- Constant of `cor:li-thickness`; it depends only on the fixed typing
(`|M|`, the explicit window `n = |h(Σ⁺)|+1`, and `|Σ|`). -/
noncomputable def corLiThicknessConst
    (H : FixedFiniteMonoidHom α M) : Nat :=
  liEnvelopeConst (Fintype.card M)
      (positiveWindowBound H + positiveWindowBound H) *
    (Fintype.card α + 2) ^ 12

/-- Degree of the polynomial in `cor:li-thickness`. -/
def corLiThicknessDegree : Nat := 12

/-- Characteristic sample in the paper's set-driven sense, obtained from
exact reconstruction plus soundness and monotonicity of `B_h`. -/
theorem isSetDrivenCharacteristicSample_of_batch_eq
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (C : Finset (Word α))
    (hsub : FixedHSubstitutable H L)
    (hchar : BatchLanguage H C = L) :
    IsSetDrivenCharacteristicSample (BatchLanguage H) L C := by
  refine ⟨?_, ?_⟩
  · intro x hx
    have := sample_consistency H C hx
    rwa [hchar] at this
  · intro K hCK hKL
    exact batchLanguage_exact_of_characteristic_subset
      H C K L hCK hKL hsub hchar

/--
Per-grammar form of `cor:li-thickness` with the constants already fixed:
`c = corLiThicknessConst H`, `d = corLiThicknessDegree` (both independent of
the grammar).
-/
theorem cor_liThickness_bound
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H)
    {N : Type u} {P : Type w}
    [Fintype N] [Fintype P] [DecidableEq N]
    (G : IndexedMixedCFG N α P) (S : N)
    (hred : IndexedMixedReduced G S)
    (hsub : FixedHSubstitutable H
      (MixedNonterminalLanguage G.toMixedRules S)) :
    (MixedNonterminalLanguage G.toMixedRules S).Nonempty ∧
    ∃ K : Finset (Word α),
      IsSetDrivenCharacteristicSample (BatchLanguage H)
        (MixedNonterminalLanguage G.toMixedRules S) K ∧
      (∑ x ∈ K, (x.length + 1)) ≤
        corLiThicknessConst H *
          (G.symbolCount + G.ordinaryThickness + 1) ^
            corLiThicknessDegree := by
  have hEqL := leastClosedLanguage_eq_mixedNonterminalLanguage
    G.toMixedRules S
  have hsub' : FixedHSubstitutable H
      (LeastClosedLanguage G.toMixedRules S) := by
    rw [hEqL]; exact hsub
  have hthick : IndexedMixedThicknessAtMost G G.ordinaryThickness :=
    ordinaryThickness_thicknessAtMost G hred.2
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hred.2 S
    exact ⟨x, hx⟩
  obtain ⟨K, hK, hnorm⟩ :=
    indexedLocallyTrivialCharacteristicData_reduced_source
      H hlocal G S hred G.ordinaryThickness hthick hsub'
  rw [hEqL] at hK
  refine ⟨K, isSetDrivenCharacteristicSample_of_batch_eq H _ K hsub hK, ?_⟩
  -- polynomial domination of the concrete envelope
  set s := G.normalizationScale with hsdef
  set τ := G.ordinaryThickness with hτdef
  have hpoly := liThicknessEnvelope_le_poly (Fintype.card M)
    (positiveWindowBound H + positiveWindowBound H) s τ
  have hscale : s ≤ Fintype.card α + 2 * G.symbolCount + 1 :=
    normalizationScale_le_symbolCount G S hred
  have hbase : s + τ + 1 ≤
      (Fintype.card α + 2) * (G.symbolCount + τ + 1) := by
    nlinarith [Nat.zero_le (Fintype.card α * G.symbolCount),
      Nat.zero_le (Fintype.card α * τ)]
  have hpow := pow_base_le_of_le_mul (d := 12) hbase
  calc (∑ x ∈ K, (x.length + 1))
      ≤ 1 + fixedWindowGrammarSizeEnvelope (Fintype.card M)
          (positiveWindowBound H + positiveWindowBound H)
          (indexedSSBNFGrammarSizeEnvelope s)
          (ssbnfThicknessEnvelope 1 1 s τ) := hnorm
    _ ≤ liEnvelopeConst (Fintype.card M)
          (positiveWindowBound H + positiveWindowBound H) *
          (s + τ + 1) ^ 12 := hpoly
    _ ≤ liEnvelopeConst (Fintype.card M)
          (positiveWindowBound H + positiveWindowBound H) *
          ((Fintype.card α + 2) ^ 12 *
            (G.symbolCount + τ + 1) ^ 12) :=
        Nat.mul_le_mul_left _ hpow
    _ = corLiThicknessConst H *
          (G.symbolCount + G.ordinaryThickness + 1) ^
            corLiThicknessDegree := by
        simp only [corLiThicknessConst, corLiThicknessDegree, hτdef]
        ring

/--
**`cor:li-thickness` (v135), manuscript-exact form.**

Let `H` be a fixed finite-monoid typing whose positive image `h(Σ⁺)` is
locally trivial (`PositiveImageSandwichTrivial`: `e·s·e = e` for every
idempotent `e` and every `s` of `h(Σ⁺)`).  There are constants `c, d`,
depending only on `H` (and the fixed alphabet), such that for **every**
reduced finite CFG `G_*` with start `S`, whose language `L` is
`h`-substitutable, `L` is nonempty and there is a characteristic sample `K`
of `L` for `B_h` (every finite `K'` with `K ⊆ K' ⊆ L` reconstructs `L`
exactly) with `‖K‖ ≤ c · (|G_*| + τ_{G_*} + 1)^d`.

Here `L` is the parse-tree language, `|G_*|` the usual symbol count and
`τ_{G_*}` the exact max–min ordinary thickness. The reconstruction typing is
the original `H`.
-/
theorem cor_liThickness_exact
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H) :
    ∃ c d : Nat,
      c = corLiThicknessConst H ∧ d = corLiThicknessDegree ∧
      ∀ {N : Type u} {P : Type w}
        [Fintype N] [Fintype P] [DecidableEq N]
        (G : IndexedMixedCFG N α P) (S : N),
        IndexedMixedReduced G S →
        FixedHSubstitutable H
          (MixedNonterminalLanguage G.toMixedRules S) →
        (MixedNonterminalLanguage G.toMixedRules S).Nonempty ∧
        ∃ K : Finset (Word α),
          IsSetDrivenCharacteristicSample (BatchLanguage H)
            (MixedNonterminalLanguage G.toMixedRules S) K ∧
          (∑ x ∈ K, (x.length + 1)) ≤
            c * (G.symbolCount + G.ordinaryThickness + 1) ^ d := by
  refine ⟨corLiThicknessConst H, corLiThicknessDegree, rfl, rfl, ?_⟩
  intro N P _ _ _ G S hred hsub
  exact cor_liThickness_bound H hlocal G S hred hsub

end CorLiThicknessExact

end TCS1
end LeanCfgProject
