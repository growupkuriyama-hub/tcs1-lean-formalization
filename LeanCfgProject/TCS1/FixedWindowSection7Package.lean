import LeanCfgProject.TCS1.FixedWindowConcreteCharacteristicData
import LeanCfgProject.TCS1.ZeroWindowEndpoint

/-!
# TCS #1 v69: paper-facing fixed-window Section 7 package

This module packages the concrete h_{k,l} construction with the already
verified characteristic-data and SSBNF-transfer bounds.

The first theorem uses the manuscript's actual fixed-h hypothesis
L in C_cf(h_{k,l}); the classical (k,l)-substitutable statement is then a
corollary via Proposition 3.2.  A final specialization records the (0,0)
endpoint explicitly.
-/

namespace LeanCfgProject
namespace TCS1

universe u w

section FixedWindowSection7Package

variable {α : Type u}
variable {N : Type w}

/-- Exact reconstruction for the concrete h_{k,l} typing under the paper's
fixed-h substitutability hypothesis. -/
theorem concreteFixedWindowCanonicalSample_characteristic_fixedH
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (k l : Nat)
    (hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    BatchLanguage
        (fixedWindowMonoidHom (α := α) k l)
        (concreteFixedWindowCanonicalSample
          terminalRule binaryRule startRule epsilonStart k l)
      =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart := by
  exact
    fixedWindowMinimalCanonicalSample_characteristic_untyped
      (fixedWindowMonoidHom (α := α) k l)
      terminalRule binaryRule startRule epsilonStart
      hsub

/--
Paper-facing Section 7 package for one already-normalized fixed-window target:
exact reconstruction and the Appendix-A transferred encoded-data bound are
returned together.
-/
theorem concreteFixedWindowSection7_package
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (k l τ g gBound cV c₁ n τR : Nat)
    (hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart))
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hN : Fintype.card N ≤ g)
    (ht :
      (@Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _)) ≤ g)
    (hb :
      (@Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _)) ≤ g)
    (hg : g ≤ gBound)
    (hτ :
      τ ≤ ssbnfThicknessEnvelope cV c₁ n τR) :
    BatchLanguage
        (fixedWindowMonoidHom (α := α) k l)
        (concreteFixedWindowCanonicalSample
          terminalRule binaryRule startRule epsilonStart k l)
      =
      UntypedStartLanguage
        terminalRule binaryRule startRule epsilonStart
    ∧
    (∑ word ∈
      concreteFixedWindowCanonicalSample
        terminalRule binaryRule startRule epsilonStart k l,
      (word.length + 1)) ≤
      fixedWindowGrammarSizeEnvelope
        (Fintype.card (FixedWindowMonoid α k l))
        (k + l) gBound
        (ssbnfThicknessEnvelope cV c₁ n τR) := by
  constructor
  · exact
      concreteFixedWindowCanonicalSample_characteristic_fixedH
        terminalRule binaryRule startRule epsilonStart
        k l hsub
  · exact
      concreteFixedWindowCanonicalSample_norm_le_ssbnf
        terminalRule binaryRule startRule epsilonStart
        k l τ g gBound cV c₁ n τR
        hshort hN ht hb hg hτ

/-- The same package for a classical Yoshinaka (k,l)-substitutable target. -/
theorem classicalFixedWindowSection7_package
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (k l τ g gBound cV c₁ n τR : Nat)
    (hwin :
      FixedWindowSubstitutable k l
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart))
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hN : Fintype.card N ≤ g)
    (ht :
      (@Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _)) ≤ g)
    (hb :
      (@Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _)) ≤ g)
    (hg : g ≤ gBound)
    (hτ :
      τ ≤ ssbnfThicknessEnvelope cV c₁ n τR) :
    BatchLanguage
        (fixedWindowMonoidHom (α := α) k l)
        (concreteFixedWindowCanonicalSample
          terminalRule binaryRule startRule epsilonStart k l)
      =
      UntypedStartLanguage
        terminalRule binaryRule startRule epsilonStart
    ∧
    (∑ word ∈
      concreteFixedWindowCanonicalSample
        terminalRule binaryRule startRule epsilonStart k l,
      (word.length + 1)) ≤
      fixedWindowGrammarSizeEnvelope
        (Fintype.card (FixedWindowMonoid α k l))
        (k + l) gBound
        (ssbnfThicknessEnvelope cV c₁ n τR) := by
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart) :=
    fixedHSubstitutable_of_fixedWindowSubstitutable
      k l
      (UntypedStartLanguage
        terminalRule binaryRule startRule epsilonStart)
      hwin
  exact
    concreteFixedWindowSection7_package
      terminalRule binaryRule startRule epsilonStart
      k l τ g gBound cV c₁ n τR
      hsub hshort hN ht hb hg hτ

/--
The endpoint r=0 is literally included in the same package.  Its semantic
hypothesis can be stated without mentioning a monoid: ordinary
substitutability on nonempty internal factors.
-/
theorem zeroWindowSection7_package
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (τ g gBound cV c₁ n τR : Nat)
    (hzero :
      NonemptyFactorSubstitutable
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart))
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hN : Fintype.card N ≤ g)
    (ht :
      (@Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _)) ≤ g)
    (hb :
      (@Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _)) ≤ g)
    (hg : g ≤ gBound)
    (hτ :
      τ ≤ ssbnfThicknessEnvelope cV c₁ n τR) :
    BatchLanguage
        (fixedWindowMonoidHom (α := α) 0 0)
        (concreteFixedWindowCanonicalSample
          terminalRule binaryRule startRule epsilonStart 0 0)
      =
      UntypedStartLanguage
        terminalRule binaryRule startRule epsilonStart
    ∧
    (∑ word ∈
      concreteFixedWindowCanonicalSample
        terminalRule binaryRule startRule epsilonStart 0 0,
      (word.length + 1)) ≤
      fixedWindowGrammarSizeEnvelope
        (Fintype.card (FixedWindowMonoid α 0 0))
        0 gBound
        (ssbnfThicknessEnvelope cV c₁ n τR) := by
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) 0 0)
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart) :=
    (fixedHSubstitutable_zeroWindow_iff_nonemptyFactorSubstitutable
      (α := α)
      (UntypedStartLanguage
        terminalRule binaryRule startRule epsilonStart)).2 hzero
  exact
    concreteFixedWindowSection7_package
      terminalRule binaryRule startRule epsilonStart
      0 0 τ g gBound cV c₁ n τR
      hsub hshort hN ht hb hg hτ

end FixedWindowSection7Package

end TCS1
end LeanCfgProject
