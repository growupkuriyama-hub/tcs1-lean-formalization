import LeanCfgProject.TCS1.FixedWindowCharacteristicDataFacade
import LeanCfgProject.TCS1.FixedWindowClassicalSubstitutability

/-!
# TCS #1 v68: concrete fixed-window characteristic data

This module specializes the Section 7 characteristic-data facade to the
actual monoid homomorphism h_{k,l} constructed in Proposition 3.2.

At this layer the abstract "respects the fixed-window summary" hypothesis has
disappeared.  Under Yoshinaka (k,l)-substitutability, the explicit canonical
sample reconstructs the untyped target exactly and satisfies the fixed-window
length/encoded-size bounds.
-/

namespace LeanCfgProject
namespace TCS1

universe u w

section FixedWindowConcreteCharacteristicData

variable {α : Type u}
variable {N : Type w}

/-- The actual minimum-length canonical sample for h_{k,l}. -/
noncomputable def concreteFixedWindowCanonicalSample
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (k l : Nat) :
    Finset (Word α) :=
  fixedWindowMinimalCanonicalSample
    (fixedWindowMonoidHom (α := α) k l)
    terminalRule binaryRule startRule epsilonStart

/--
Every word in the actual h_{k,l} canonical sample obeys the Lemma 7.2 common
length envelope.
-/
theorem mem_concreteFixedWindowCanonicalSample_length_le
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (k l τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    {word : Word α}
    (hword :
      word ∈
        concreteFixedWindowCanonicalSample
          terminalRule binaryRule startRule epsilonStart
          k l) :
    word.length ≤
      fixedWindowWitnessLengthEnvelope
        (@Fintype.card
          (ActiveTypedSymbol
            (ConcreteTypedActive
              (fixedWindowMonoidHom (α := α) k l)
              terminalRule binaryRule startRule))
          (Fintype.ofFinite _))
        (k + l) (Fintype.card N) τ := by
  classical
  letI :
      Fintype
        (ActiveTypedSymbol
          (ConcreteTypedActive
            (fixedWindowMonoidHom (α := α) k l)
            terminalRule binaryRule startRule)) :=
    Fintype.ofFinite _
  exact
    mem_fixedWindowMinimalCanonicalSample_length_le
      (fixedWindowMonoidHom (α := α) k l)
      terminalRule binaryRule startRule epsilonStart
      k l
      (fixedWindowMonoidHom_respects (α := α) k l)
      τ hshort hword

/--
Encoded-size bound for the actual h_{k,l} canonical sample.
All auxiliary finite-index instances are constructed internally.
-/
theorem concreteFixedWindowCanonicalSample_norm_le
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (k l τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ) :
    (∑ word ∈
      concreteFixedWindowCanonicalSample
        terminalRule binaryRule startRule epsilonStart k l,
      (word.length + 1)) ≤
    fixedWindowCharacteristicEnvelope
      (Fintype.card (FixedWindowMonoid α k l))
      (k + l)
      (Fintype.card N)
      (@Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _))
      (@Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _))
      τ := by
  classical
  let H :=
    fixedWindowMonoidHom (α := α) k l
  let Active :=
    ConcreteTypedActive
      H terminalRule binaryRule startRule
  letI : Fintype (ActiveTypedSymbol Active) :=
    Fintype.ofFinite _
  letI :
      Fintype
        (ActiveTypedTerminalIndex H terminalRule Active) :=
    Fintype.ofFinite _
  letI :
      Fintype
        (ActiveTypedBinaryIndex binaryRule Active) :=
    Fintype.ofFinite _
  letI :
      Fintype (UntypedTerminalRuleIndex terminalRule) :=
    Fintype.ofFinite _
  letI :
      Fintype (UntypedBinaryRuleIndex binaryRule) :=
    Fintype.ofFinite _
  exact
    fixedWindowMinimalCanonicalSample_norm_le
      H terminalRule binaryRule startRule epsilonStart
      k l
      (fixedWindowMonoidHom_respects (α := α) k l)
      τ hshort

/--
Exact characteristicity for the underlying untyped target follows directly
from classical (k,l)-substitutability.
-/
theorem concreteFixedWindowCanonicalSample_characteristic
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (k l : Nat)
    (hwin :
      FixedWindowSubstitutable k l
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    BatchLanguage
        (fixedWindowMonoidHom (α := α) k l)
        (concreteFixedWindowCanonicalSample
          terminalRule binaryRule startRule epsilonStart k l)
      =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart := by
  classical
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
    fixedWindowMinimalCanonicalSample_characteristic_untyped
      (fixedWindowMonoidHom (α := α) k l)
      terminalRule binaryRule startRule epsilonStart
      hsub

/--
Concrete Section 7 package: exact reconstruction plus the explicit encoded
characteristic-data bound, with no abstract monoid-summary hypothesis left.
-/
theorem concreteFixedWindowCanonicalSample_package
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (k l τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hwin :
      FixedWindowSubstitutable k l
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
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
      fixedWindowCharacteristicEnvelope
        (Fintype.card (FixedWindowMonoid α k l))
        (k + l)
        (Fintype.card N)
        (@Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _))
        (@Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _))
        τ := by
  constructor
  · exact
      concreteFixedWindowCanonicalSample_characteristic
        terminalRule binaryRule startRule epsilonStart
        k l hwin
  · exact
      concreteFixedWindowCanonicalSample_norm_le
        terminalRule binaryRule startRule epsilonStart
        k l τ hshort

/--
Appendix-A transfer form for the actual h_{k,l} sample.
-/
theorem concreteFixedWindowCanonicalSample_norm_le_ssbnf
    [Fintype α] [Fintype N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (k l τ g gBound cV c₁ n τR : Nat)
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
    (∑ word ∈
      concreteFixedWindowCanonicalSample
        terminalRule binaryRule startRule epsilonStart k l,
      (word.length + 1)) ≤
    fixedWindowGrammarSizeEnvelope
      (Fintype.card (FixedWindowMonoid α k l))
      (k + l) gBound
      (ssbnfThicknessEnvelope cV c₁ n τR) := by
  classical
  let H :=
    fixedWindowMonoidHom (α := α) k l
  let Active :=
    ConcreteTypedActive
      H terminalRule binaryRule startRule
  letI : Fintype (ActiveTypedSymbol Active) :=
    Fintype.ofFinite _
  letI :
      Fintype
        (ActiveTypedTerminalIndex H terminalRule Active) :=
    Fintype.ofFinite _
  letI :
      Fintype
        (ActiveTypedBinaryIndex binaryRule Active) :=
    Fintype.ofFinite _
  letI :
      Fintype (UntypedTerminalRuleIndex terminalRule) :=
    Fintype.ofFinite _
  letI :
      Fintype (UntypedBinaryRuleIndex binaryRule) :=
    Fintype.ofFinite _
  exact
    fixedWindowMinimalCanonicalSample_norm_le_ssbnf
      H terminalRule binaryRule startRule epsilonStart
      k l
      (fixedWindowMonoidHom_respects (α := α) k l)
      τ g gBound cV c₁ n τR
      hshort hN ht hb hg hτ

end FixedWindowConcreteCharacteristicData

end TCS1
end LeanCfgProject
