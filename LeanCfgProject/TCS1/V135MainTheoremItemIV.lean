import LeanCfgProject.TCS1.V135LiThicknessExactCorollary
import LeanCfgProject.TCS1.MainTheoremMaterializedPackage

/-!
# TCS #1 v135: `thm:main` item (iv) attached to the verified learner

Manuscript `thm:main` (v135) fixes `h`, one set-driven reconstruction operator
`B_h` and one conservative sequential learner `A_h`, and states in item (iv):

> if the positive image semigroup `h(Σ⁺)` is locally trivial, then for every
> nonempty target the sample in (ii) can be chosen polynomial in `|G_*|` and
> `τ_{G_*}` for any reduced CFG `G_*` representing that target.
> The polynomials … may depend on the fixed `h` and `Σ`, but not on `G_*`.

This module does **not** build a new learner.  It ties the manuscript-exact
corollary `cor_liThickness_exact` to the already verified materialized
learner package `indexedFixedH_learning_materialized_core`:

* the characteristic sample of item (iv) is characteristic (in the full
  set-driven sense) for exactly the operator `BatchLanguage H`, i.e. the
  `B_h` whose hypotheses the materialized conservative learner `A_h` outputs;
* the same target is Gold-identified by that learner on every positive
  presentation (item (iii), reused);
* constants `c = corLiThicknessConst H`, `d = 12` are fixed before the target
  grammar is quantified, i.e. they depend only on `H` (`|M|`, the explicit
  window `n = |h(Σ⁺)|+1`) and `|Σ|`.

Scope (kept separate, not claimed here): items (i), (ii), (iii), (v) are
covered by the existing `MainTheorem*Package` modules; the clause "in
particular for every fixed-window typing `h_{k,l}`" follows from item (iv)
together with the positive-window theorem in `V128PositiveWindowKernelForward`
and is recorded separately once its concrete-window `PositiveImageSandwichTrivial`
instance is connected; polynomial *time* of the normalization in
`prop:thick-ssbnf-normal` is not part of item (iv).
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section V135MainTheoremItemIV

variable {α : Type v} [Fintype α] [DecidableEq α]
variable {M : Type q} [Monoid M] [Fintype M] [DecidableEq M]

/--
**`thm:main` (iv), attached to the verified learner.**

Under local triviality of `h(Σ⁺)`, with constants depending only on `H`:
for every reduced finite CFG `G_*` with start `S` whose (nonempty) language
`L` is `h`-substitutable,

1. `L` is nonempty;
2. `L` has a characteristic sample for `B_h = BatchLanguage H` of encoded
   size at most `c · (|G_*| + τ_{G_*} + 1)^d`;
3. on every positive presentation `datum` of `L`, the materialized
   conservative learner `A_h` (whose hypotheses are interpreted through the
   same `B_h`) stabilizes on a correct hypothesis.
-/
theorem thm_main_item_iv
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
        (∃ K : Finset (Word α),
          IsSetDrivenCharacteristicSample (BatchLanguage H)
            (MixedNonterminalLanguage G.toMixedRules S) K ∧
          (∑ x ∈ K, (x.length + 1)) ≤
            c * (G.symbolCount + G.ordinaryThickness + 1) ^ d)
        ∧
        (∀ datum : Nat → Word α,
          (∀ n, datum n ∈ MixedNonterminalLanguage G.toMixedRules S) →
          (∀ x, x ∈ MixedNonterminalLanguage G.toMixedRules S →
            ∃ n, x ∈ concreteAccumulatedSample datum n) →
          MaterializedGoldConclusion H
            (MixedNonterminalLanguage G.toMixedRules S) datum) := by
  refine ⟨corLiThicknessConst H, corLiThicknessDegree, rfl, rfl, ?_⟩
  intro N P _ _ _ G S hred hsub
  obtain ⟨hne, hK⟩ := cor_liThickness_bound H hlocal G S hred hsub
  refine ⟨hne, hK, ?_⟩
  intro datum hpos hcov
  have hEqL := leastClosedLanguage_eq_mixedNonterminalLanguage
    G.toMixedRules S
  have hsub' : FixedHSubstitutable H
      (LeastClosedLanguage G.toMixedRules S) := by
    rw [hEqL]; exact hsub
  have hpos' : ∀ n, datum n ∈ LeastClosedLanguage G.toMixedRules S := by
    intro n; rw [hEqL]; exact hpos n
  have hcov' : ∀ x, x ∈ LeastClosedLanguage G.toMixedRules S →
      ∃ n, x ∈ concreteAccumulatedSample datum n := by
    intro x hx; rw [hEqL] at hx; exact hcov x hx
  obtain ⟨_, _, _, hgold⟩ :=
    indexedFixedH_learning_materialized_core
      H G S hsub' datum hpos' hcov'
  rw [hEqL] at hgold
  exact hgold

end V135MainTheoremItemIV

end TCS1
end LeanCfgProject
