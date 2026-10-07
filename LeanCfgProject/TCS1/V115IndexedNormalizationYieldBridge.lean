import LeanCfgProject.TCS1.V115LocalThicknessBound
import LeanCfgProject.TCS1.IndexedConcreteSSBNFNormalization

/-!
# TCS #1 v115: the indexed CFG-to-SSBNF yield bridge

The v115 Corollary 7.5 ends by invoking the polynomial
thickness-preserving normalization of a general reduced CFG R into
SSBNF. The v69 normalization implementation derives actual terminal
words in the concrete productive/reachable reduced grammar, while the
fixed-h characteristic-sample construction uses `UntypedDerives`
(the binary/terminal fragment).

This module removes that representational gap. Every derivation in
the concrete final reduced unit-free grammar is a terminal/binary
derivation; no epsilon or unit constructor can occur there.
Consequently the already formalized indexed normalization thickness
bound is directly available as the precise `hshort` premise of
`v115_locallyTrivial_sampleNorm_le_ordinaryThickness`.

It does not yet assert a sample bound directly in the source CFG's
encoding size: that remaining step needs the normalization *rule and
state count* estimates in addition to the yield bound.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V115IndexedNormalizationYieldBridge

variable {N : Type u} {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/--
The normalized non-start state type is a finite subtype of the
finite front-end grammar. Install that derived finiteness instance
globally so the indexed canonical-witness statement itself can name
the actual finite witness set without an additional assumption.
-/
noncomputable instance v115IndexedReducedStateFintype
    (G : IndexedMixedCFG N α P)
    (start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G)) :
    Fintype
      (ReducedUnitFreeState
        (indexedFiniteFrontEndGrammar G) start) :=
  Fintype.ofFinite _

/--
No epsilon or unit derivation can occur in the final concrete
productive/reachable trim. Its terminal language embeds directly
into the SSBNF non-start derivation relation used by the learner.
-/
theorem v115_reducedUnitFree_to_untyped
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G)
    {A : ReducedUnitFreeState G start}
    {word : Word α}
    (d :
      BinaryNullableDerives
        (reducedUnitFreeGrammar G start) A word) :
    UntypedDerives
      (reducedUnitFreeGrammar G start).terminalRule
      (reducedUnitFreeGrammar G start).binaryRule
      A word := by
  induction d with
  | terminal h =>
      exact UntypedDerives.terminal h
  | epsilon h =>
      exact False.elim h
  | unit h _ _ =>
      exact False.elim h
  | binary h _ _ ihB ihC =>
      exact UntypedDerives.binary h ihB ihC

/--
The actual normalized grammar satisfies the non-start `hshort`
premise, with the same explicit SSBNF envelope from Proposition 7.4.
Here `G` is a finitely indexed source CFG, not an abstract grammar
whose normalization contract is taken as an additional assumption.
-/
theorem v115_indexedNormalization_untypedYieldBound
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
    ∀ A :
        ReducedUnitFreeState
          (indexedFiniteFrontEndGrammar G) start,
      ∃ word : Word α,
        UntypedDerives
          (reducedUnitFreeGrammar
            (indexedFiniteFrontEndGrammar G) start).terminalRule
          (reducedUnitFreeGrammar
            (indexedFiniteFrontEndGrammar G) start).binaryRule
          A word
        ∧ word.length ≤
          ssbnfThicknessEnvelope
            1 1 G.normalizationScale τR := by
  have hbound :=
    indexed_proposition74_concreteReducedTrim_thickness
      G τR hn hsource start
  intro A
  obtain ⟨word, d, hlength⟩ := hbound A
  exact
    ⟨word,
      v115_reducedUnitFree_to_untyped
        (indexedFiniteFrontEndGrammar G) start d,
      hlength⟩

end V115IndexedNormalizationYieldBridge
end TCS1
end LeanCfgProject
