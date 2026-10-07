import LeanCfgProject.TCS1.FixedWindowConcreteMonoid
import LeanCfgProject.TCS1.FixedWindowCharacteristicDataFacade

/-!
# TCS #1 v121: locally-trivial / fixed-window learning bridge

The new v121 algebraic proposition uses the classical semigroup fact that a
locally trivial positive image yields a finite prefix/suffix window whose
positive-word kernel refines the given typing.  The semigroup theorem itself is
cited from Pin in the manuscript and is kept as an explicit external boundary.

This file formalizes the paper-specific consequence of that classical input:
positive-word kernel refinement is enough to make the original typing respect
the fixed-window summary, and therefore the existing Section 7 canonical-sample
bounds apply directly to the original typing H (not merely to h_{k,l}).
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V121LocallyTrivialBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Positive-word kernel refinement from the concrete fixed-window typing to H. -/
def PositiveWindowKernelRefines
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat) : Prop :=
  ∀ x y : Word α,
    x ≠ [] →
    y ≠ [] →
    (fixedWindowMonoidHom (α := α) k l).h x =
      (fixedWindowMonoidHom (α := α) k l).h y →
    H.h x = H.h y

/--
The kernel inclusion used in v121 Proposition "locally trivial typings and
fixed windows" implies the exact semantic contract required by the already
verified fixed-window characteristic-data machinery.
-/
theorem respectsFixedWindowSummary_of_positiveKernelRefinement
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat)
    (href : PositiveWindowKernelRefines H k l) :
    RespectsFixedWindowSummary H k l := by
  intro x y hsame
  rcases hsame with hshort | hlong
  · exact congrArg H.h hshort.2.symm
  · have hthreshold : 0 < fixedWindowThreshold k l := by
      simp [fixedWindowThreshold]
    have hxpos : 0 < x.length :=
      lt_of_lt_of_le hthreshold hlong.1
    have hypos : 0 < y.length :=
      lt_of_lt_of_le hthreshold hlong.2.1
    have hxne : x ≠ [] :=
      List.ne_nil_of_length_pos hxpos
    have hyne : y ≠ [] :=
      List.ne_nil_of_length_pos hypos
    have hsame' : SameFixedWindowSummary k l x y :=
      Or.inr hlong
    have hwindow :
        (fixedWindowMonoidHom (α := α) k l).h x =
          (fixedWindowMonoidHom (α := α) k l).h y :=
      fixedWindowMonoidHom_respects k l x y hsame'
    exact href x y hxne hyne hwindow

/--
Paper-facing quantitative bridge: once the classical algebraic step has
produced a positive kernel refinement, the existing canonical sample for H is
both characteristic for the untyped target and bounded by the fixed-window
envelope.
-/
theorem characteristicPackage_of_positiveWindowKernelRefinement
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
    (href : PositiveWindowKernelRefines H k l)
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
  exact
    fixedWindowMinimalCanonicalSample_untyped_package
      H terminalRule binaryRule startRule epsilonStart
      k l
      (respectsFixedWindowSummary_of_positiveKernelRefinement
        H k l href)
      τ hshort hsub

end V121LocallyTrivialBridge

end TCS1
end LeanCfgProject
