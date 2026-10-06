import LeanCfgProject.TCS1.V115IndexedCharacteristicData
import LeanCfgProject.TCS1.IndexedNormalizationLanguage
import LeanCfgProject.TCS1.FixedWindowCharacteristicDataFacade

/-!
# TCS #1 v115: characteristic data for the original indexed CFG language

This module attaches the verified polynomial norm of the concrete
normalized canonical witness finset to its *exact-reconstruction*
property, using the existing source-to-SSBNF language-equivalence
theorem.  It is the source-CFG end-to-end version of the quantitative
assertion in v115 Corollary 7.5 (and main theorem item (iv)).

The data-size bound is stated as a concrete polynomial expression.
Only assumptions intrinsic to the manuscript remain: finite indexed
reduced CFG input, bounded ordinary short yields, a productive
source start, local triviality of the finite positive-image typing,
and fixed-h substitutability of the generated target.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w x

section V115IndexedCharacteristicPackage

variable {N : Type u} {α : Type v} {P : Type w}
variable {M : Type x} [Monoid M] [Fintype M]
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α] [Nonempty α]

/-- Explicit polynomial for the indexed source-CFG sample norm, at fixed h. -/
noncomputable def v115IndexedNormEnvelope
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (τR : Nat) : Nat :=
  let s := indexedSSBNFGrammarSizeEnvelope G.normalizationScale
  typedThicknessWitnessCountEnvelope
    (Fintype.card M) s s s *
      (((s * Fintype.card M + 1) *
        fixedWindowTypedYieldBound
          (v115PositiveImageCard H + v115PositiveImageCard H)
          s (ssbnfThicknessEnvelope 1 1 G.normalizationScale τR))
        + 1)

/--
The canonical data set of the normalized grammar reconstructs the
*original source-start language* and is polynomially bounded in
the finite indexed grammar's source size and ordinary thickness.
-/
theorem v115_indexedLocallyTrivial_characteristic_package
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (G : IndexedMixedCFG N α P)
    (sourceStart : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules sourceStart
          ∧ u ≠ [])
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage G.toMixedRules A)
        τR)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules sourceStart)) :
    let B := indexedFiniteFrontEndGrammar G
    let start := indexedProductiveUnitFreeState_of_nonempty
      G sourceStart hprod
    let t := reducedSSBNFTerminalRule B start
    let b := reducedSSBNFBinaryRule B start
    let s := reducedSSBNFStartRule B start
    let keepEmpty := [] ∈ LeastClosedLanguage G.toMixedRules sourceStart
    BatchLanguage H
      (fixedWindowMinimalCanonicalSample H t b s keepEmpty)
      =
    LeastClosedLanguage G.toMixedRules sourceStart
      ∧
    (∑ word ∈
      fixedWindowMinimalCanonicalSample H t b s keepEmpty,
      (word.length + 1))
    ≤
    v115IndexedNormEnvelope H G τR := by
  classical
  dsimp only
  let B := indexedFiniteFrontEndGrammar G
  let start := indexedProductiveUnitFreeState_of_nonempty
    G sourceStart hprod
  let t := reducedSSBNFTerminalRule B start
  let b := reducedSSBNFBinaryRule B start
  let s := reducedSSBNFStartRule B start
  let keepEmpty := [] ∈ LeastClosedLanguage G.toMixedRules sourceStart
  let NT := ReducedUnitFreeState B start
  letI : Fintype NT := Fintype.ofFinite _
  letI : Fintype (ActiveTypedSymbol (ConcreteTypedActive H t b s)) :=
    Fintype.ofFinite _
  letI : Fintype (ActiveTypedTerminalIndex H t
      (ConcreteTypedActive H t b s)) := Fintype.ofFinite _
  letI : Fintype (ActiveTypedBinaryIndex b
      (ConcreteTypedActive H t b s)) := Fintype.ofFinite _
  letI : Fintype (UntypedTerminalRuleIndex t) := Fintype.ofFinite _
  letI : Fintype (UntypedBinaryRuleIndex b) := Fintype.ofFinite _
  have hlang :
      UntypedStartLanguage t b s keepEmpty =
        LeastClosedLanguage G.toMixedRules sourceStart := by
    simpa only [B, start, t, b, s, keepEmpty] using
      (indexedReducedSSBNF_untypedStartLanguage_eq_source
        G sourceStart hprod)
  have hsubNorm :
      FixedHSubstitutable H
        (UntypedStartLanguage t b s keepEmpty) := by
    rw [hlang]
    exact hsub
  have hcharacteristic :
      BatchLanguage H
        (fixedWindowMinimalCanonicalSample H t b s keepEmpty) =
        LeastClosedLanguage G.toMixedRules sourceStart := by
    calc
      BatchLanguage H
        (fixedWindowMinimalCanonicalSample H t b s keepEmpty) =
        UntypedStartLanguage t b s keepEmpty :=
        fixedWindowMinimalCanonicalSample_characteristic_untyped
          H t b s keepEmpty hsubNorm
      _ = LeastClosedLanguage G.toMixedRules sourceStart :=
        hlang
  have hminimal :
      CanonicalChoiceMinimality
        H t b s keepEmpty
        (ConcreteTypedActive H t b s)
        (concreteTypedActive_minimalChoices H t b s keepEmpty) :=
    concreteTypedActive_minimalChoices_minimality
      H t b s keepEmpty
  have hnorm :
      (∑ word ∈ fixedWindowMinimalCanonicalSample H t b s keepEmpty,
        (word.length + 1)) ≤
      v115IndexedNormEnvelope H G τR := by
    have hbound :=
      v115_indexedLocallyTrivial_canonicalSampleNorm
        H hlocal G τR hn hsource start keepEmpty
        (concreteTypedActive_minimalChoices H t b s keepEmpty)
        hminimal
    simpa only [fixedWindowMinimalCanonicalSample,
      v115IndexedNormEnvelope, B, start, t, b, s, keepEmpty] using hbound
  exact ⟨hcharacteristic, hnorm⟩

end V115IndexedCharacteristicPackage
end TCS1
end LeanCfgProject
