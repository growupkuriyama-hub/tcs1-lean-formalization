import LeanCfgProject.TCS1.V115SSBNFRegularIntersection
import LeanCfgProject.TCS1.IndexedNormalizationLanguage

/-!
# TCS #1 v115: regular filtering of a finite indexed source CFG

Compose the explicit automaton-product SSBNF grammar with the
paper's verified normalization of an arbitrary finite indexed CFG.
The initial source symbol must have a nonempty successful yield:
this is exactly the constructive/productive normalization branch.
The epsilon word is separately preserved by the optional start rule.

There is no generic CFL-closure axiom here. The finite-state product
grammar is explicitly the output witness. The empty-only and empty
source-language cases of full Proposition 3.2(ii) remain separate
degenerate branches for the final unrestricted claim audit.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w x y

section V115IndexedRegularIntersection

variable {N : Type u} {α : Type v} {P : Type w}
variable {M : Type x} {F : Type y}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]
variable [Monoid M] [Fintype M]
variable [Monoid F] [Fintype F]

/--
Source-level Proposition 3.2(ii), on the nonempty-productive branch:
the filtered language has an explicit binary/terminal grammar with
non-start states (A,p,q), is exactly the original finite indexed CFG
language intersected with the finite-monoid recognized regular language,
and satisfies substitutability for H x G.
-/
theorem v115_indexedRegularIntersection_nonempty
    (R : IndexedMixedCFG N α P)
    (sourceStart : N)
    (hprod :
      ∃ w : Word α,
        w ∈ LeastClosedLanguage R.toMixedRules sourceStart
          ∧ w ≠ [])
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α F)
    (Acc : Set F)
    (hsub :
      FixedHSubstitutable
        H (LeastClosedLanguage R.toMixedRules sourceStart)) :
    let B := indexedFiniteFrontEndGrammar R
    let start := indexedProductiveUnitFreeState_of_nonempty
      R sourceStart hprod
    let t := reducedSSBNFTerminalRule B start
    let b := reducedSSBNFBinaryRule B start
    let s := reducedSSBNFStartRule B start
    let eps := [] ∈ LeastClosedLanguage R.toMixedRules sourceStart
    let filtered :=
      UntypedStartLanguage
        (v115FilterTerminal (v115MonoidTransition G) t)
        (v115FilterBinary b)
        (v115FilterStart s 1 (fun m => m ∈ Acc))
        (eps ∧ (1 : F) ∈ Acc)
    filtered =
      LeastClosedLanguage R.toMixedRules sourceStart
        ∩ RecognizedPreimage G Acc
    ∧
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G) filtered := by
  let B := indexedFiniteFrontEndGrammar R
  let start := indexedProductiveUnitFreeState_of_nonempty
    R sourceStart hprod
  let t := reducedSSBNFTerminalRule B start
  let b := reducedSSBNFBinaryRule B start
  let s := reducedSSBNFStartRule B start
  let eps := [] ∈ LeastClosedLanguage R.toMixedRules sourceStart
  let filtered :=
    UntypedStartLanguage
      (v115FilterTerminal (v115MonoidTransition G) t)
      (v115FilterBinary b)
      (v115FilterStart s 1 (fun m => m ∈ Acc))
      (eps ∧ (1 : F) ∈ Acc)
  change
    filtered =
      LeastClosedLanguage R.toMixedRules sourceStart
        ∩ RecognizedPreimage G Acc
    ∧
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G) filtered
  have hbase :
      UntypedStartLanguage t b s eps =
        LeastClosedLanguage R.toMixedRules sourceStart := by
    simpa only [t, b, s, B, start, eps] using
      (indexedReducedSSBNF_untypedStartLanguage_eq_source
        R sourceStart hprod)
  have hfilter :
      filtered =
        UntypedStartLanguage t b s eps
          ∩ RecognizedPreimage G Acc :=
    v115MonoidFilteredSSBNF_language G Acc t b s eps
  have hsubNorm :
      FixedHSubstitutable H
        (UntypedStartLanguage t b s eps) := by
    rw [hbase]
    exact hsub
  constructor
  · rw [hfilter, hbase]
  · exact
      v115_ssbnf_regular_filter_fixedH
        H G Acc t b s eps hsubNorm

end V115IndexedRegularIntersection

end TCS1
end LeanCfgProject
