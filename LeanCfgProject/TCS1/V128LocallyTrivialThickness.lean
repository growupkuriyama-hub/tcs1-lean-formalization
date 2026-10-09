import LeanCfgProject.TCS1.V128PositiveWindowKernelForward
import LeanCfgProject.TCS1.FixedWindowCharacteristicDataFacade

/-!
# TCS #1 v128: locally trivial typings and ordinary-thickness data

This file connects the newly closed forward direction of
`prop:li-window` to the characteristic-data machinery that was already
verified for fixed windows.

For a fixed typing H whose positive image is locally trivial, put

  n = |h(Σ⁺)| + 1.

The forward theorem gives positive-word kernel refinement by the concrete
`(n,n)` window.  Short fixed-window summaries are literal word equality and
long summaries are positive, so this refinement supplies the full
`RespectsFixedWindowSummary H n n` contract.  The existing Section 7
witness-length, sample-norm, and SSBNF-normalization bounds can therefore be
reused directly for H.

The statements below are the representation-level quantitative core of
Corollary `cor:li-thickness`.  They deliberately reuse the existing
normalization interfaces instead of duplicating those proofs.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V128LocallyTrivialThickness

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- The locally trivial hypothesis supplies the exact Section 7 window
contract at `n=|h(Σ⁺)|+1`. -/
theorem locallyTrivial_explicitWindow_contract
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H) :
    RespectsFixedWindowSummary
      H (positiveWindowBound H) (positiveWindowBound H) :=
  positiveImageTrivial_implies_respects_explicitWindow H hlocal

/--
Characteristic-data package for a reduced SSBNF presentation under a locally
trivial positive image.

This is the fixed-window package specialized at the explicit manuscript
window, but the reconstructed language and the learner batch remain typed by
the original H.
-/
theorem locallyTrivialMinimalCanonicalSample_untyped_package
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
    (hlocal : PositiveImageSandwichTrivial H)
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
        (positiveWindowBound H + positiveWindowBound H)
        (Fintype.card N)
        (Fintype.card (UntypedTerminalRuleIndex terminalRule))
        (Fintype.card (UntypedBinaryRuleIndex binaryRule))
        τ := by
  exact
    fixedWindowMinimalCanonicalSample_untyped_package
      H terminalRule binaryRule startRule epsilonStart
      (positiveWindowBound H) (positiveWindowBound H)
      (locallyTrivial_explicitWindow_contract H hlocal)
      τ hshort hsub

/--
The encoded norm of the same characteristic sample obeys the already
verified SSBNF-normalization envelope.  Here `sourceSize` and `τR` are the
size/thickness parameters of the pre-normalized representation, while the
hypotheses `hg` and `hτ` are exactly the quantitative normalization
obligations used by the existing transfer theorem.
-/
theorem locallyTrivialMinimalCanonicalSample_norm_le_ssbnf
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
    (hlocal : PositiveImageSandwichTrivial H)
    (τ g gBound cV c₁ sourceSize τR : Nat)
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
      τ ≤ ssbnfThicknessEnvelope cV c₁ sourceSize τR) :
    (∑ word ∈
      fixedWindowMinimalCanonicalSample
        H terminalRule binaryRule startRule epsilonStart,
      (word.length + 1)) ≤
      fixedWindowGrammarSizeEnvelope
        (Fintype.card M)
        (positiveWindowBound H + positiveWindowBound H)
        gBound
        (ssbnfThicknessEnvelope cV c₁ sourceSize τR) := by
  exact
    fixedWindowMinimalCanonicalSample_norm_le_ssbnf
      H terminalRule binaryRule startRule epsilonStart
      (positiveWindowBound H) (positiveWindowBound H)
      (locallyTrivial_explicitWindow_contract H hlocal)
      τ g gBound cV c₁ sourceSize τR
      hshort hN ht hb hg hτ

/--
Combined manuscript-facing core of `cor:li-thickness`: exact
reconstruction of the original untyped target together with the
normalization-transferred encoded-size bound.
-/
theorem locallyTrivialCharacteristicData_ssbnf_package
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
    (hlocal : PositiveImageSandwichTrivial H)
    (τ g gBound cV c₁ sourceSize τR : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart))
    (hN : Fintype.card N ≤ g)
    (ht :
      Fintype.card (UntypedTerminalRuleIndex terminalRule) ≤ g)
    (hb :
      Fintype.card (UntypedBinaryRuleIndex binaryRule) ≤ g)
    (hg : g ≤ gBound)
    (hτ :
      τ ≤ ssbnfThicknessEnvelope cV c₁ sourceSize τR) :
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
      fixedWindowGrammarSizeEnvelope
        (Fintype.card M)
        (positiveWindowBound H + positiveWindowBound H)
        gBound
        (ssbnfThicknessEnvelope cV c₁ sourceSize τR) := by
  constructor
  · exact
      fixedWindowMinimalCanonicalSample_characteristic_untyped
        H terminalRule binaryRule startRule epsilonStart hsub
  · exact
      locallyTrivialMinimalCanonicalSample_norm_le_ssbnf
        H terminalRule binaryRule startRule epsilonStart
        hlocal τ g gBound cV c₁ sourceSize τR
        hshort hN ht hb hg hτ

end V128LocallyTrivialThickness

end TCS1
end LeanCfgProject
