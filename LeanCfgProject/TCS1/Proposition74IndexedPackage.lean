import LeanCfgProject.TCS1.IndexedSection7Bridge

/-!
# TCS #1 v79: end-to-end indexed package for Proposition 7.4

The manuscript's Proposition 7.4 is stated for an arbitrary reduced CFG and
asserts polynomial control of both the normalized grammar size and its
thickness while preserving the generated language.

The development already proves all ingredients separately:

* exact source-language preservation for the concrete productive/reachable
  start-separated SSBNF normalization;
* a cubic grammar-size envelope in the explicit indexed encoding scale;
* the quadratic shortest-yield/thickness envelope
  `1 + n_G^2 * (tau_R + 1)`.

This file packages those facts in one theorem directly over the actual
normalized grammar used by the Section 7 bridge.  It is the theorem-facing
counterpart of the v79 Proposition 7.4 statement.  Polynomial-time execution
is represented by the explicit finite constructions themselves; this package
records the semantic and quantitative obligations checked by Lean.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section Proposition74IndexedPackage

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/--
End-to-end semantic/quantitative package for the concrete normalized SSBNF
presentation attached to an indexed finite CFG.

The hypothesis `hsource` is exactly the formal form of saying that the
source grammar has thickness at most `tauR`: every source nonterminal has a
terminal yield of length at most `tauR`.  For a reduced source grammar this
is the property supplied by the manuscript's `tau_R`.
-/
theorem indexed_proposition74_full_package
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR) :
    let start :=
      indexedProductiveUnitFreeState_of_nonempty
        G A hprod
    let Nf :=
      ReducedUnitFreeState
        (indexedFiniteFrontEndGrammar G) start
    UntypedStartLanguage
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G) start)
        ([] ∈ LeastClosedLanguage G.toMixedRules A)
      =
        LeastClosedLanguage G.toMixedRules A
    ∧
    (@Fintype.card Nf (Fintype.ofFinite _))
      ≤ indexedSSBNFGrammarSizeEnvelope
          G.normalizationScale
    ∧
    (@Fintype.card
        (UntypedTerminalRuleIndex
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
      ≤ indexedSSBNFGrammarSizeEnvelope
          G.normalizationScale
    ∧
    (@Fintype.card
        (UntypedBinaryRuleIndex
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
      ≤ indexedSSBNFGrammarSizeEnvelope
          G.normalizationScale
    ∧
    (∀ X : Nf,
      ∃ z : Word α,
        UntypedDerives
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start)
          X z
        ∧
        z.length ≤
          ssbnfThicknessEnvelope
            1 1 G.normalizationScale τR)
    ∧
    ssbnfThicknessEnvelope
        1 1 G.normalizationScale τR
      =
    1 + G.normalizationScale^2 * thicknessBar τR := by
  dsimp
  let start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G) :=
    indexedProductiveUnitFreeState_of_nonempty
      G A hprod
  let Nf :=
    ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G) start
  letI : Fintype Nf := Fintype.ofFinite _

  have hlang :
      UntypedStartLanguage
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFStartRule
            (indexedFiniteFrontEndGrammar G) start)
          ([] ∈ LeastClosedLanguage G.toMixedRules A)
        =
      LeastClosedLanguage G.toMixedRules A := by
    simpa [start] using
      indexedReducedSSBNF_untypedStartLanguage_eq_source
        G A hprod

  have hN :
      Fintype.card Nf ≤
        indexedSSBNFGrammarSizeEnvelope
          G.normalizationScale := by
    simpa [Nf] using
      indexedReducedSSBNF_state_card_le_grammarSizeEnvelope
        G start

  have ht :
      (@Fintype.card
        (UntypedTerminalRuleIndex
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
        ≤
      indexedSSBNFGrammarSizeEnvelope
        G.normalizationScale :=
    indexedReducedSSBNF_terminalRule_card_le_grammarSizeEnvelope
      G start

  have hb :
      (@Fintype.card
        (UntypedBinaryRuleIndex
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start))
        (Fintype.ofFinite _))
        ≤
      indexedSSBNFGrammarSizeEnvelope
        G.normalizationScale :=
    indexedReducedSSBNF_binaryRule_card_le_grammarSizeEnvelope
      G start

  have hshort :
      ∀ X : Nf,
        ∃ z : Word α,
          UntypedDerives
            (reducedSSBNFTerminalRule
              (indexedFiniteFrontEndGrammar G) start)
            (reducedSSBNFBinaryRule
              (indexedFiniteFrontEndGrammar G) start)
            X z
          ∧
          z.length ≤
            ssbnfThicknessEnvelope
              1 1 G.normalizationScale τR := by
    simpa [Nf, start] using
      indexedReducedSSBNF_shortWitness
        G A hprod τR hn hsource

  have henv :
      ssbnfThicknessEnvelope
          1 1 G.normalizationScale τR
        =
      1 + G.normalizationScale^2 * thicknessBar τR :=
    indexed_proposition74_explicit_envelope
      G τR

  exact
    ⟨hlang, hN, ht, hb, hshort, henv⟩

end Proposition74IndexedPackage

end TCS1
end LeanCfgProject
