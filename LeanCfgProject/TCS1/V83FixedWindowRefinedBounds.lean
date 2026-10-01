import LeanCfgProject.TCS1.V83TypedThicknessWitnessBounds

/-!
# TCS #1 v83: refined fixed-window constants

The v83 manuscript writes theta_{k,l}(G) for the fixed-window typed-yield
bound and sharpens the context/witness constants from the archived v79
envelopes to

  |u_X| + |v_X| <= (Nt-1) theta
  |w| <= (Nt+1) theta.

This module derives those revised constants from the already verified
fixed-window typed-yield theorem plus the v83 generic typed-thickness path
argument.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V83FixedWindowRefinedBounds

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- v83 notation for the previously verified fixed-window typed-yield bound. -/
abbrev fixedWindowTheta := fixedWindowTypedYieldBound

/-- The fixed-window theta bound is positive whenever the source thickness is. -/
theorem fixedWindowTheta_pos
    {r N τ : Nat}
    (hτ : 1 ≤ τ) :
    1 ≤ fixedWindowTheta r N τ := by
  by_cases hr : r = 0
  · subst r
    simpa using hτ
  · have hrpos : 1 ≤ r := by omega
    simp only [fixedWindowTheta, fixedWindowTypedYieldBound, if_neg hr]
    exact le_trans hrpos (Nat.le_add_right r _)

/--
Revised v83 context bound for the concrete productive/reachable typed trim.
-/
theorem concreteTypedActive_minimalContext_length_le_fixedWindow_v83
    [Fintype N]
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
    (hrespect : RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (X : N × M)
    (hX :
      ConcreteTypedActive
        H terminalRule binaryRule startRule X) :
    let C :=
      concreteTypedActive_minimalChoices
        H terminalRule binaryRule startRule epsilonStart
    (C.left X).length + (C.right X).length ≤
      (Fintype.card
          (ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)) - 1) *
        fixedWindowTheta (k + l) (Fintype.card N) τ := by
  classical
  let C :=
    concreteTypedActive_minimalChoices
      H terminalRule binaryRule startRule epsilonStart
  let minimal :=
    concreteTypedActive_minimalChoices_minimality
      H terminalRule binaryRule startRule epsilonStart
  let reach :=
    concreteTypedActive_structuralReachability
      H terminalRule binaryRule startRule epsilonStart C
  let trim :=
    concreteTypedActive_trimClosure
      H terminalRule binaryRule startRule
  have hω :
      ∀ Y : N × M,
        ConcreteTypedActive
            H terminalRule binaryRule startRule Y →
        (C.omega Y).length ≤
          fixedWindowTheta
            (k + l) (Fintype.card N) τ := by
    intro Y hY
    exact
      canonicalOmega_length_le_fixedWindow
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)
        C minimal trim
        k l hrespect τ hshort
        Y hY
  exact
    canonicalContext_length_le_of_typedYieldBound
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      H terminalRule binaryRule startRule epsilonStart
      C minimal reach
      (fixedWindowTheta (k + l) (Fintype.card N) τ)
      hω X hX

/--
Revised v83 common witness-length bound for fixed windows.
-/
theorem concreteTypedActive_minimalCanonicalWitnessWords_length_le_fixedWindow_v83
    [Fintype N]
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
    (hrespect : RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hτ : 1 ≤ τ)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    {word : Word α}
    (hword :
      word ∈
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart
          (ConcreteTypedActive
            H terminalRule binaryRule startRule)
          (concreteTypedActive_minimalChoices
            H terminalRule binaryRule startRule epsilonStart)) :
    word.length ≤
      (Fintype.card
          (ActiveTypedSymbol
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)) + 1) *
        fixedWindowTheta
          (k + l) (Fintype.card N) τ := by
  classical
  let C :=
    concreteTypedActive_minimalChoices
      H terminalRule binaryRule startRule epsilonStart
  let minimal :=
    concreteTypedActive_minimalChoices_minimality
      H terminalRule binaryRule startRule epsilonStart
  let reach :=
    concreteTypedActive_structuralReachability
      H terminalRule binaryRule startRule epsilonStart C
  let trim :=
    concreteTypedActive_trimClosure
      H terminalRule binaryRule startRule
  have hω :
      ∀ Y : N × M,
        ConcreteTypedActive
            H terminalRule binaryRule startRule Y →
        (C.omega Y).length ≤
          fixedWindowTheta
            (k + l) (Fintype.card N) τ := by
    intro Y hY
    exact
      canonicalOmega_length_le_fixedWindow
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule)
        C minimal trim
        k l hrespect τ hshort
        Y hY
  exact
    canonicalWitnessWords_length_le_typedThickness
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      H terminalRule binaryRule startRule epsilonStart
      C minimal reach
      (fixedWindowTheta (k + l) (Fintype.card N) τ)
      (fixedWindowTheta_pos hτ)
      hω hword

end V83FixedWindowRefinedBounds

end TCS1
end LeanCfgProject
