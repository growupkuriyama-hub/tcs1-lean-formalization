import LeanCfgProject.TCS1.V135LiThicknessExactCorollary
import LeanCfgProject.TCS1.V128SubstringTabulatedGrammar

/-!
# TCS #1 v135: item (iv) for the manuscript's v116 constructor `B_h`

The v135 manuscript describes `B_h` by the Clark-style substring grammar with
tabulated (B), (U), (L), (S), (ε) rules (v116).  The verified theorem
`v116TabulatedBatchLanguage_eq_batchLanguage` (CI #858) shows that, for every
finite sample `K`, this explicit finite grammar generates exactly
`BatchLanguage H K`.  Hence characteristicity transfers verbatim, and the
polynomial characteristic data of `cor:li-thickness` are characteristic for
the manuscript's own operator.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section V135ItemIVv116

variable {α : Type v} [Fintype α] [DecidableEq α]
variable {M : Type q} [Monoid M] [Fintype M]

/-- The v116 tabulated operator and `BatchLanguage` are the same operator. -/
theorem v116TabulatedBatchLanguage_eq_batchLanguage_fun
    (H : FixedFiniteMonoidHom α M) :
    v116TabulatedBatchLanguage H = BatchLanguage H :=
  funext (v116TabulatedBatchLanguage_eq_batchLanguage H)

/-- Characteristic samples for the two presentations of `B_h` coincide. -/
theorem isSetDrivenCharacteristicSample_v116_iff
    (H : FixedFiniteMonoidHom α M) (L : Set (Word α)) (C : Finset (Word α)) :
    IsSetDrivenCharacteristicSample (v116TabulatedBatchLanguage H) L C ↔
      IsSetDrivenCharacteristicSample (BatchLanguage H) L C := by
  rw [v116TabulatedBatchLanguage_eq_batchLanguage_fun H]

/-- `cor:li-thickness` for the manuscript's v116 operator `B_h`. -/
theorem cor_liThickness_bound_v116
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
      IsSetDrivenCharacteristicSample (v116TabulatedBatchLanguage H)
        (MixedNonterminalLanguage G.toMixedRules S) K ∧
      (∑ x ∈ K, (x.length + 1)) ≤
        corLiThicknessConst H *
          (G.symbolCount + G.ordinaryThickness + 1) ^
            corLiThicknessDegree := by
  obtain ⟨hne, K, hK, hnorm⟩ := cor_liThickness_bound H hlocal G S hred hsub
  exact ⟨hne, K, (isSetDrivenCharacteristicSample_v116_iff H _ K).2 hK, hnorm⟩

end V135ItemIVv116

end TCS1
end LeanCfgProject
