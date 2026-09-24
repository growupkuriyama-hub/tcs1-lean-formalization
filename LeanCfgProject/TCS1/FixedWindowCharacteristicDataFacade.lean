import LeanCfgProject.TCS1.ConcreteTypedTrimming
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage
import LeanCfgProject.TCS1.CanonicalWitnessCounting

/-!
# TCS #1 v68: characteristic-data facade for the fixed-window section

This module packages the concrete productive/reachable typed trim, the
minimum-length canonical witness choices, the Lemma 7.2 witness-length bound,
the four-family witness count, and exact reconstruction.

For an arbitrary fixed finite typing H satisfying the fixed-window summary
contract, the resulting explicit canonical witness finset is therefore both

* characteristic for the reduced typed target (under fixed-H substitutability),
  and
* bounded by the exact arithmetic envelope used in Section 7.

Specializing H to the concrete h_{k,l} construction is a separate algebraic
bridge.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section FixedWindowCharacteristicDataFacade

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- The minimum-length canonical sample for the concrete typed trim. -/
noncomputable def fixedWindowMinimalCanonicalSample
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    Finset (Word α) :=
  canonicalWitnessFinset
    H terminalRule binaryRule startRule epsilonStart
    (ConcreteTypedActive
      H terminalRule binaryRule startRule)
    (concreteTypedActive_minimalChoices
      H terminalRule binaryRule startRule epsilonStart)

/--
Every word in the concrete minimum-length sample satisfies the exact
Lemma 7.2 common envelope with Nt equal to the number of surviving typed
symbols.
-/
theorem mem_fixedWindowMinimalCanonicalSample_length_le
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    [Fintype
      (ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    {word : Word α}
    (hword :
      word ∈
        fixedWindowMinimalCanonicalSample
          H terminalRule binaryRule startRule epsilonStart) :
    word.length ≤
      fixedWindowWitnessLengthEnvelope
        (Fintype.card
          (ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)))
        (k + l) (Fintype.card N) τ := by
  classical
  have hwCanonical :
      word ∈
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart
          (ConcreteTypedActive
            H terminalRule binaryRule startRule)
          (concreteTypedActive_minimalChoices
            H terminalRule binaryRule startRule epsilonStart) := by
    exact
      (mem_canonicalWitnessFinset_iff
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)
        (concreteTypedActive_minimalChoices
          H terminalRule binaryRule startRule epsilonStart)
        word).1 hword
  exact
    concreteTypedActive_minimalCanonicalWitnessWords_length_le_fixedWindow
      H terminalRule binaryRule startRule epsilonStart
      k l hrespect τ hshort hwCanonical

/--
Encoded-size bound for the actual minimum-length canonical sample.

The right-hand side is exactly the explicit Section 7 arithmetic envelope,
with m=|M|, N the number of underlying non-start symbols, and terminal/binary
production counts supplied by their finite index types.
-/
theorem fixedWindowMinimalCanonicalSample_norm_le
    [Fintype α] [DecidableEq α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    [Fintype
      (ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedTerminalIndex H terminalRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedBinaryIndex binaryRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype (UntypedTerminalRuleIndex terminalRule)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)]
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ) :
    (∑ word ∈
      fixedWindowMinimalCanonicalSample
        H terminalRule binaryRule startRule epsilonStart,
      (word.length + 1)) ≤
    fixedWindowCharacteristicEnvelope
      (Fintype.card M)
      (k + l)
      (Fintype.card N)
      (Fintype.card (UntypedTerminalRuleIndex terminalRule))
      (Fintype.card (UntypedBinaryRuleIndex binaryRule))
      τ := by
  classical
  apply
    canonicalWitnessFinset_fixedWindow_sampleNorm_bound
      H terminalRule binaryRule startRule epsilonStart
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      (concreteTypedActive_minimalChoices
        H terminalRule binaryRule startRule epsilonStart)
      (k + l) τ
  intro word hword
  exact
    mem_fixedWindowMinimalCanonicalSample_length_le
      H terminalRule binaryRule startRule epsilonStart
      k l hrespect τ hshort hword

/--
Coarser grammar-size form of the encoded-sample estimate.

If one natural number g bounds the underlying non-start symbols and both
production families, the actual canonical sample is bounded by the paper's
single-parameter grammar-size envelope.
-/
theorem fixedWindowMinimalCanonicalSample_norm_le_grammarSize
    [Fintype α] [DecidableEq α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    [Fintype
      (ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedTerminalIndex H terminalRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedBinaryIndex binaryRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype (UntypedTerminalRuleIndex terminalRule)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)]
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ g : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hN : Fintype.card N ≤ g)
    (ht :
      Fintype.card (UntypedTerminalRuleIndex terminalRule) ≤ g)
    (hb :
      Fintype.card (UntypedBinaryRuleIndex binaryRule) ≤ g) :
    (∑ word ∈
      fixedWindowMinimalCanonicalSample
        H terminalRule binaryRule startRule epsilonStart,
      (word.length + 1)) ≤
    fixedWindowGrammarSizeEnvelope
      (Fintype.card M) (k + l) g τ := by
  have h0 :=
    fixedWindowMinimalCanonicalSample_norm_le
      H terminalRule binaryRule startRule epsilonStart
      k l hrespect τ hshort
  exact
    le_trans h0
      (fixedWindowCharacteristicEnvelope_le_grammarSize
        hN ht hb)

/--
Transfer the actual canonical sample bound through arbitrary grammar-size and
thickness envelopes supplied by normalization.
-/
theorem fixedWindowMinimalCanonicalSample_norm_le_transfer
    [Fintype α] [DecidableEq α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    [Fintype
      (ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedTerminalIndex H terminalRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedBinaryIndex binaryRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype (UntypedTerminalRuleIndex terminalRule)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)]
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ g gBound τBound : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hN : Fintype.card N ≤ g)
    (ht :
      Fintype.card (UntypedTerminalRuleIndex terminalRule) ≤ g)
    (hb :
      Fintype.card (UntypedBinaryRuleIndex binaryRule) ≤ g)
    (hg : g ≤ gBound)
    (hτ : τ ≤ τBound) :
    (∑ word ∈
      fixedWindowMinimalCanonicalSample
        H terminalRule binaryRule startRule epsilonStart,
      (word.length + 1)) ≤
    fixedWindowGrammarSizeEnvelope
      (Fintype.card M) (k + l) gBound τBound := by
  have h0 :=
    fixedWindowMinimalCanonicalSample_norm_le_grammarSize
      H terminalRule binaryRule startRule epsilonStart
      k l hrespect τ g hshort hN ht hb
  exact
    le_trans h0
      (fixedWindow_complexity_transfer hg hτ)

/--
Appendix-A specialization: substitute the explicit SSBNF thickness envelope
directly into the actual canonical-sample estimate.
-/
theorem fixedWindowMinimalCanonicalSample_norm_le_ssbnf
    [Fintype α] [DecidableEq α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    [Fintype
      (ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedTerminalIndex H terminalRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedBinaryIndex binaryRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype (UntypedTerminalRuleIndex terminalRule)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)]
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ g gBound cV c₁ n τR : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hN : Fintype.card N ≤ g)
    (ht :
      Fintype.card (UntypedTerminalRuleIndex terminalRule) ≤ g)
    (hb :
      Fintype.card (UntypedBinaryRuleIndex binaryRule) ≤ g)
    (hg : g ≤ gBound)
    (hτ :
      τ ≤ ssbnfThicknessEnvelope cV c₁ n τR) :
    (∑ word ∈
      fixedWindowMinimalCanonicalSample
        H terminalRule binaryRule startRule epsilonStart,
      (word.length + 1)) ≤
    fixedWindowGrammarSizeEnvelope
      (Fintype.card M) (k + l) gBound
      (ssbnfThicknessEnvelope cV c₁ n τR) := by
  exact
    fixedWindowMinimalCanonicalSample_norm_le_transfer
      H terminalRule binaryRule startRule epsilonStart
      k l hrespect
      τ g gBound
      (ssbnfThicknessEnvelope cV c₁ n τR)
      hshort hN ht hb hg hτ

/--
The concrete minimum-length canonical sample is characteristic for the reduced
typed target whenever that target is fixed-H substitutable.
-/
theorem fixedWindowMinimalCanonicalSample_characteristic
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (hsub :
      FixedHSubstitutable H
        (ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart
          (ConcreteTypedActive
            H terminalRule binaryRule startRule))) :
    BatchLanguage H
        (fixedWindowMinimalCanonicalSample
          H terminalRule binaryRule startRule epsilonStart)
      =
    ReducedTypedLanguage
      H terminalRule binaryRule startRule epsilonStart
      (ConcreteTypedActive
        H terminalRule binaryRule startRule) := by
  classical
  exact
    exact_reconstruction_of_canonicalWitnessFinset
      H terminalRule binaryRule startRule epsilonStart
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      (concreteTypedActive_minimalChoices
        H terminalRule binaryRule startRule epsilonStart)
      hsub

/--
Paper-facing characteristicity statement against the underlying untyped
start-separated target language.
-/
theorem fixedWindowMinimalCanonicalSample_characteristic_untyped
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    BatchLanguage H
        (fixedWindowMinimalCanonicalSample
          H terminalRule binaryRule startRule epsilonStart)
      =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart := by
  have hsubReduced :=
    concreteTypedActive_fixedHSubstitutable
      H terminalRule binaryRule startRule epsilonStart hsub
  calc
    BatchLanguage H
        (fixedWindowMinimalCanonicalSample
          H terminalRule binaryRule startRule epsilonStart)
      =
        ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart
          (ConcreteTypedActive
            H terminalRule binaryRule startRule) :=
      fixedWindowMinimalCanonicalSample_characteristic
        H terminalRule binaryRule startRule epsilonStart
        hsubReduced
    _ =
        UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart :=
      concreteTypedActive_language_eq_untyped
        H terminalRule binaryRule startRule epsilonStart

/--
Combined characteristic-data package for the fixed-window quantitative
section: exact reconstruction and the explicit encoded-size envelope.
-/
theorem fixedWindowMinimalCanonicalSample_package
    [Fintype α] [DecidableEq α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    [Fintype
      (ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedTerminalIndex H terminalRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedBinaryIndex binaryRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype (UntypedTerminalRuleIndex terminalRule)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)]
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hsub :
      FixedHSubstitutable H
        (ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart
          (ConcreteTypedActive
            H terminalRule binaryRule startRule))) :
    BatchLanguage H
        (fixedWindowMinimalCanonicalSample
          H terminalRule binaryRule startRule epsilonStart)
      =
      ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)
    ∧
    (∑ word ∈
      fixedWindowMinimalCanonicalSample
        H terminalRule binaryRule startRule epsilonStart,
      (word.length + 1)) ≤
      fixedWindowCharacteristicEnvelope
        (Fintype.card M)
        (k + l)
        (Fintype.card N)
        (Fintype.card (UntypedTerminalRuleIndex terminalRule))
        (Fintype.card (UntypedBinaryRuleIndex binaryRule))
        τ := by
  constructor
  · exact
      fixedWindowMinimalCanonicalSample_characteristic
        H terminalRule binaryRule startRule epsilonStart hsub
  · exact
      fixedWindowMinimalCanonicalSample_norm_le
        H terminalRule binaryRule startRule epsilonStart
        k l hrespect τ hshort

/--
Combined Section 7 package directly against the underlying untyped target:
the minimum-length canonical sample reconstructs the target exactly and obeys
the explicit fixed-window characteristic-data envelope.
-/
theorem fixedWindowMinimalCanonicalSample_untyped_package
    [Fintype α] [DecidableEq α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    [Fintype
      (ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedTerminalIndex H terminalRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedBinaryIndex binaryRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype (UntypedTerminalRuleIndex terminalRule)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)]
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    BatchLanguage H
        (fixedWindowMinimalCanonicalSample
          H terminalRule binaryRule startRule epsilonStart)
      =
      UntypedStartLanguage
        terminalRule binaryRule startRule epsilonStart
    ∧
    (∑ word ∈
      fixedWindowMinimalCanonicalSample
        H terminalRule binaryRule startRule epsilonStart,
      (word.length + 1)) ≤
      fixedWindowCharacteristicEnvelope
        (Fintype.card M)
        (k + l)
        (Fintype.card N)
        (Fintype.card (UntypedTerminalRuleIndex terminalRule))
        (Fintype.card (UntypedBinaryRuleIndex binaryRule))
        τ := by
  constructor
  · exact
      fixedWindowMinimalCanonicalSample_characteristic_untyped
        H terminalRule binaryRule startRule epsilonStart hsub
  · exact
      fixedWindowMinimalCanonicalSample_norm_le
        H terminalRule binaryRule startRule epsilonStart
        k l hrespect τ hshort

end FixedWindowCharacteristicDataFacade

end TCS1
end LeanCfgProject
