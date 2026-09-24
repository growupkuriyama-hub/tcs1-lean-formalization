import LeanCfgProject.TCS1.ReducedTypedRuleBridge
import LeanCfgProject.TCS1.FixedWindowContextSemantic
import LeanCfgProject.TCS1.FixedWindowLemma72Facade

/-!
# TCS #1 v68: reduced typed reaching contexts

This file connects the generic dependency-spine semantics of Lemma 7.2 to the
actual reduced yield-typed refinement.

Surviving typed symbols are treated as the finite subtype
`ActiveTypedSymbol Active`.  A structural reachability certificate records a
binary-rule spine from some non-start child of a start rule to every active
typed symbol.  Lemma 7.1 supplies bounded replacement yields for all sibling
symbols on that spine; cycle shortening then yields the paper's
`Nt * B_{k,l}(G)` terminal-context bound.

The only remaining representation-level obligation is to obtain the structural
reachability certificate from the concrete productive/reachable trimming
construction.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section FixedWindowReducedContextFacade

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/--
Structural reachability of every surviving typed symbol from a non-start child
of a start rule.
-/
structure ActiveTypedStructuralReachability
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (Active : N × M → Prop) : Prop where
  spine :
    ∀ X : ActiveTypedSymbol Active,
      ∃ R : ActiveTypedSymbol Active,
        ∃ left right : Word α,
          ∃ path : List (ActiveTypedSymbol Active),
            ∃ siblings : List Nat,
              startRule R.1.1
              ∧
              ReachingSpine
                (ActiveTypedTerminalRule H terminalRule Active)
                (ActiveTypedBinaryRule binaryRule Active)
                R X left right path siblings

/--
Lemma 7.1 can be applied to every productive active typed symbol encountered
as an off-path sibling.
-/
theorem activeTyped_productive_bounded_yield
    [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop)
    (trim :
      SuccessfulTypedTrimClosure
        H terminalRule binaryRule Active)
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (Y : ActiveTypedSymbol Active)
    {z₀ : Word α}
    (d₀ :
      UntypedDerives
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Y z₀) :
    ∃ z : Word α,
      UntypedDerives
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Y z
      ∧
      z.length ≤
        fixedWindowTypedYieldBound
          (k + l) (Fintype.card N) τ := by
  classical
  letI : DecidableEq N := Classical.decEq N

  have d₀Reduced :
      ReducedTypedDerives
        H terminalRule binaryRule Active Y.1 z₀ :=
    activeUntypedDerives_to_reducedTypedDerives
      H terminalRule binaryRule Active d₀

  have d₀Full :
      TypedDerives H terminalRule binaryRule Y.1 z₀ :=
    reducedTypedDerives_to_typedDerives
      H terminalRule binaryRule Active d₀Reduced

  obtain ⟨z, dzFull, hz⟩ :=
    exists_fixedWindow_bounded_typed_yield
      H terminalRule binaryRule
      d₀Full k l hrespect τ hshort

  have dzReduced :
      ReducedTypedDerives
        H terminalRule binaryRule Active Y.1 z :=
    trim.restrict Y.2 dzFull

  have dzActiveRaw :=
    reducedTypedDerives_to_activeUntypedDerives
      H terminalRule binaryRule Active dzReduced

  have dzActive :
      UntypedDerives
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Y z := by
    simpa using dzActiveRaw

  exact ⟨z, dzActive, hz⟩

/--
First displayed conclusion of Lemma 7.2.

Every active typed symbol has a terminal reaching context of total length at
most `Nt * B_{k,l}(G)`, where `Nt` is the number of active typed symbols.
-/
theorem exists_fixedWindow_reduced_short_reaching_context
    [Fintype N]
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (trim :
      SuccessfulTypedTrimClosure
        H terminalRule binaryRule Active)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (X : N × M)
    (hX : Active X) :
    ∃ left right : Word α,
      (∀ {z : Word α},
        ReducedTypedDerives
          H terminalRule binaryRule Active X z →
        ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active
          (left ++ z ++ right))
      ∧
      left.length + right.length ≤
        Fintype.card (ActiveTypedSymbol Active) *
          fixedWindowTypedYieldBound
            (k + l) (Fintype.card N) τ := by
  classical
  letI : DecidableEq N := Classical.decEq N
  letI : DecidableEq (ActiveTypedSymbol Active) :=
    Classical.decEq _

  let XT : ActiveTypedSymbol Active := ⟨X, hX⟩
  obtain ⟨R, left₀, right₀, path₀, siblings₀,
      hstart, spine₀⟩ :=
    reach.spine XT

  let B :=
    fixedWindowTypedYieldBound
      (k + l) (Fintype.card N) τ

  have hbounded :
      ∀ (Y : ActiveTypedSymbol Active) {z₀ : Word α},
        UntypedDerives
          (ActiveTypedTerminalRule H terminalRule Active)
          (ActiveTypedBinaryRule binaryRule Active)
          Y z₀ →
        ∃ z : Word α,
          UntypedDerives
            (ActiveTypedTerminalRule H terminalRule Active)
            (ActiveTypedBinaryRule binaryRule Active)
            Y z
          ∧ z.length ≤ B := by
    intro Y z₀ dY
    exact
      activeTyped_productive_bounded_yield
        H terminalRule binaryRule Active trim
        k l hrespect τ hshort Y dY

  obtain ⟨left₁, right₁, siblings₁,
      spine₁, heach₁⟩ :=
    reachingSpine_replace_siblings_by_bounded_yields
      (ActiveTypedTerminalRule H terminalRule Active)
      (ActiveTypedBinaryRule binaryRule Active)
      B spine₀ hbounded

  obtain ⟨left', right', path', siblings',
      spine', hnodup, heach', hlen⟩ :=
    reachingSpine_nodup_context_exists
      (ActiveTypedTerminalRule H terminalRule Active)
      (ActiveTypedBinaryRule binaryRule Active)
      B spine₁ heach₁

  refine ⟨left', right', ?_, ?_⟩
  intro z dX
  have dXActiveRaw :=
    reducedTypedDerives_to_activeUntypedDerives
      H terminalRule binaryRule Active dX
  have dXActive :
      UntypedDerives
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        XT z := by
    simpa [XT] using dXActiveRaw

  have dRootActive :
      UntypedDerives
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        R (left' ++ z ++ right') :=
    reachingSpine_plug
      (ActiveTypedTerminalRule H terminalRule Active)
      (ActiveTypedBinaryRule binaryRule Active)
      spine' dXActive

  have dRootReduced :
      ReducedTypedDerives
        H terminalRule binaryRule Active
        R.1 (left' ++ z ++ right') :=
    activeUntypedDerives_to_reducedTypedDerives
      H terminalRule binaryRule Active dRootActive

  exact
    ReducedTypedStartDerives.nonempty
      hstart R.2 dRootReduced
  · simpa [B] using hlen

/--
Quantitative data package for Lemma 7.2 obtained from structural reachability,
Lemma 7.1, and canonical minimality.
-/
theorem canonicalYieldContextBounds_fixedWindow_of_structural_reachability
    [Fintype N]
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    (trim :
      SuccessfulTypedTrimClosure
        H terminalRule binaryRule Active)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ) :
    CanonicalYieldContextBounds
      H terminalRule binaryRule startRule epsilonStart Active C
      (Fintype.card (ActiveTypedSymbol Active))
      (fixedWindowTypedYieldBound
        (k + l) (Fintype.card N) τ) := by
  classical
  letI : DecidableEq N := Classical.decEq N

  apply
    canonicalYieldContextBounds_fixedWindow_of_context_alternatives
      H terminalRule binaryRule startRule epsilonStart
      Active C minimal trim
      k l
      (Fintype.card (ActiveTypedSymbol Active))
      hrespect τ hshort
  intro X hX
  exact
    exists_fixedWindow_reduced_short_reaching_context
      Active H terminalRule binaryRule startRule epsilonStart
      trim reach
      k l hrespect τ hshort X hX

/--
Full paper-facing witness-length conclusion of Lemma 7.2 from structural
reachability.

Combining the active-symbol reaching-context construction with canonical
minimality gives the common bound for every actual word in
`CanonicalWitnessWords`.
-/
theorem canonicalWitnessWords_length_le_fixedWindow_of_structural_reachability
    [Fintype N]
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    (trim :
      SuccessfulTypedTrimClosure
        H terminalRule binaryRule Active)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
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
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart Active C) :
    word.length ≤
      fixedWindowWitnessLengthEnvelope
        (Fintype.card (ActiveTypedSymbol Active))
        (k + l) (Fintype.card N) τ := by
  classical
  letI : DecidableEq N := Classical.decEq N
  have bounds :=
    canonicalYieldContextBounds_fixedWindow_of_structural_reachability
      Active H terminalRule binaryRule startRule epsilonStart
      C minimal trim reach
      k l hrespect τ hshort
  exact
    canonicalWitnessWords_length_le_fixedWindow
      H terminalRule binaryRule startRule epsilonStart
      Active C
      (Fintype.card (ActiveTypedSymbol Active))
      (k + l) (Fintype.card N) τ
      bounds hword

end FixedWindowReducedContextFacade

end TCS1
end LeanCfgProject
