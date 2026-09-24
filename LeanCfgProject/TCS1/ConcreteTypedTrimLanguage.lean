import LeanCfgProject.TCS1.ConcreteTypedTrimming

/-!
# TCS #1 v68: language preservation of the concrete typed trim

The paper forms the full yield-typed refinement of a start-separated SSBNF
grammar and then removes typed symbols that are not productive/reachable.

For the concrete active predicate in ConcreteTypedTrimming, this file proves
that the reduced typed start language is exactly the original untyped
start-separated language. Thus fixed-H substitutability of the target can be
transported to the reduced typed target without an additional hypothesis.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section ConcreteTypedTrimLanguage

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Start semantics of the underlying start-separated untyped SSBNF grammar. -/
inductive UntypedStartDerives
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    Word α → Prop
  | nonempty
      {A : N} {word : Word α}
      (hstart : startRule A)
      (d : UntypedDerives terminalRule binaryRule A word) :
      UntypedStartDerives
        terminalRule binaryRule startRule epsilonStart word
  | epsilon
      (heps : epsilonStart) :
      UntypedStartDerives
        terminalRule binaryRule startRule epsilonStart []

/-- Language of the underlying start-separated untyped grammar. -/
def UntypedStartLanguage
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    Set (Word α) :=
  {word |
    UntypedStartDerives
      terminalRule binaryRule startRule epsilonStart word}

/--
Erasing the concrete reduced typed refinement gives an untyped start
derivation.
-/
theorem concreteReducedTypedStartDerives_erase
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    {word : Word α}
    (d :
      ReducedTypedStartDerives
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)
        word) :
    UntypedStartDerives
      terminalRule binaryRule startRule epsilonStart word := by
  cases d with
  | @nonempty A μ word hstart hactive dTyped =>
      exact
        UntypedStartDerives.nonempty
          hstart
          (typedDerives_erase
            H terminalRule binaryRule
            (reducedTypedDerives_to_typedDerives
              H terminalRule binaryRule
              (ConcreteTypedActive
                H terminalRule binaryRule startRule)
              dTyped))
  | epsilon heps =>
      exact UntypedStartDerives.epsilon heps

/--
Every untyped start derivation lifts to the full typed refinement and, because
its root is a start child with a successful yield, survives the concrete
productive/reachable trim.
-/
theorem untypedStartDerives_to_concreteReducedTyped
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    {word : Word α}
    (d :
      UntypedStartDerives
        terminalRule binaryRule startRule epsilonStart word) :
    ReducedTypedStartDerives
      H terminalRule binaryRule startRule epsilonStart
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      word := by
  cases d with
  | @nonempty A word hstart dUntyped =>
      have dFull :
          TypedDerives
            H terminalRule binaryRule
            (A, H.h word) word :=
        untypedDerives_lift
          H terminalRule binaryRule dUntyped
      have hactive :
          ConcreteTypedActive
            H terminalRule binaryRule startRule
            (A, H.h word) :=
        ProductiveTypedReachable.start
          hstart ⟨word, dFull⟩
      have dReduced :
          ReducedTypedDerives
            H terminalRule binaryRule
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)
            (A, H.h word) word :=
        (concreteTypedActive_trimClosure
          H terminalRule binaryRule startRule).restrict
          hactive dFull
      exact
        ReducedTypedStartDerives.nonempty
          hstart hactive dReduced
  | epsilon heps =>
      exact ReducedTypedStartDerives.epsilon heps

/-- Exact start-language preservation by the concrete typed trim. -/
theorem concreteTypedActive_language_eq_untyped
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)
      =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart := by
  apply Set.ext
  intro word
  constructor
  · intro hword
    exact
      concreteReducedTypedStartDerives_erase
        H terminalRule binaryRule startRule epsilonStart hword
  · intro hword
    exact
      untypedStartDerives_to_concreteReducedTyped
        H terminalRule binaryRule startRule epsilonStart hword

/--
Fixed-H substitutability of the underlying target transfers literally to the
concrete reduced typed target because the two start languages are equal.
-/
theorem concreteTypedActive_fixedHSubstitutable
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    FixedHSubstitutable H
      (ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)) := by
  rw [concreteTypedActive_language_eq_untyped
    H terminalRule binaryRule startRule epsilonStart]
  exact hsub

end ConcreteTypedTrimLanguage

end TCS1
end LeanCfgProject
