import LeanCfgProject.TCS1.IndexedNormalizationFacade
import LeanCfgProject.TCS1.EpsilonFreeProductiveTrim
import LeanCfgProject.TCS1.UnitFreeReachableTrim
import LeanCfgProject.TCS1.SeparatedStartSSBNF

/-!
# TCS #1 v69: concrete indexed SSBNF normalization

The direct indexed normalization facade already proves the polynomial
thickness theorem but leaves the productive family after epsilon elimination
and the final trimming maps abstract.  Here those parameters are instantiated
by the actual semantic subtypes:

* ProductiveEpsilonFreeState after epsilon elimination;
* ProductiveUnitFreeState after unit elimination; and
* ReducedUnitFreeState for the final productive/reachable trim.

Thus the thickness half of Proposition 7.4 is stated directly for the actual
final reduced grammar.  A second theorem transports the same bound through
the fresh separated-start presentation.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedConcreteSSBNFNormalization

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/--
Direct Proposition 7.4 thickness statement for the actual final
productive/reachable trim of the indexed front-end grammar.
-/
theorem indexed_proposition74_concreteReducedTrim_thickness
    (G : IndexedMixedCFG N α P)
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage G.toMixedRules A)
        τR)
    (start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G)) :
    YieldBound
      (fun A :
        ReducedUnitFreeState
          (indexedFiniteFrontEndGrammar G) start =>
        {w | BinaryNullableDerives
          (reducedUnitFreeGrammar
            (indexedFiniteFrontEndGrammar G) start)
          A w})
      (ssbnfThicknessEnvelope
        1 1 G.normalizationScale τR) := by
  have hambient :
      YieldBound
        (fun A :
          ReducedUnitFreeState
            (indexedFiniteFrontEndGrammar G) start =>
          {w | UnitFreeDerives
            (indexedFiniteFrontEndGrammar G)
            A.1.1 w})
        (ssbnfThicknessEnvelope
          1 1 G.normalizationScale τR) := by
    exact
      indexed_proposition74_thickness
        G τR hn hsource
        (fun A :
          ProductiveEpsilonFreeState
            (indexedFiniteFrontEndGrammar G) =>
          A.1)
        (fun A :
          ReducedUnitFreeState
            (indexedFiniteFrontEndGrammar G) start =>
          productiveUnitFree_to_productiveEpsilonFree
            (indexedFiniteFrontEndGrammar G)
            A.1)
        (productiveEpsilonFree_allHaveNonempty
          (indexedFiniteFrontEndGrammar G))
  intro A
  obtain ⟨w, hw, hlen⟩ := hambient A
  have hp :
      BinaryNullableDerives
        (productiveUnitFreeGrammar
          (indexedFiniteFrontEndGrammar G))
        A.1 w :=
    (productiveTrimDerives_iff_unitFree
      (indexedFiniteFrontEndGrammar G)
      A.1 w).2 hw
  have hr :
      BinaryNullableDerives
        (reducedUnitFreeGrammar
          (indexedFiniteFrontEndGrammar G) start)
        A w :=
    (reducedTrimDerives_iff_productive
      (indexedFiniteFrontEndGrammar G)
      start A w).2 hp
  exact ⟨w, hr, hlen⟩

/--
Adding the fresh separated start does not change the shortest-yield bound of
any non-start symbol in the final SSBNF presentation.
-/
theorem indexed_proposition74_separatedNonstart_thickness
    (G : IndexedMixedCFG N α P)
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage G.toMixedRules A)
        τR)
    (start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G))
    (keepEmpty : Prop) :
    YieldBound
      (fun A :
        ReducedUnitFreeState
          (indexedFiniteFrontEndGrammar G) start =>
        {w | BinaryNullableDerives
          (separatedStartGrammar
            (indexedFiniteFrontEndGrammar G)
            start keepEmpty)
          (some A) w})
      (ssbnfThicknessEnvelope
        1 1 G.normalizationScale τR) := by
  have hred :=
    indexed_proposition74_concreteReducedTrim_thickness
      G τR hn hsource start
  intro A
  obtain ⟨w, hw, hlen⟩ := hred A
  exact
    ⟨w,
      reducedDerives_to_separated
        (indexedFiniteFrontEndGrammar G)
        start keepEmpty hw,
      hlen⟩

end IndexedConcreteSSBNFNormalization

end TCS1
end LeanCfgProject
