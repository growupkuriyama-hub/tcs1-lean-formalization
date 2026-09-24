import LeanCfgProject.TCS1.LinearSpineSemantic
import LeanCfgProject.TCS1.LinearCanonicalWitnessBounds
import LeanCfgProject.TCS1.FixedWindowReducedContextFacade
import LeanCfgProject.TCS1.MinimalReducedWitnessChoices

/-!
# TCS #1: linear-spine semantics to canonical witness bounds

This module closes the semantic gap between the linear-spine SSBNF shape and
the actual minimum canonical witnesses used by the reconstruction theorem.

For the surviving yield-typed symbols, assume the reduced typed grammar has
the linear-spine shape of Appendix A and every active typed symbol is
structurally reachable from a start child.  Then:

* every minimum productive yield has length at most the number n_t of active
  typed symbols;
* every minimum terminal reaching context has total length at most 2 n_t;
* every canonical witness therefore has linear length; and
* the actual canonical witness finset satisfies the explicit polynomial
  encoded-size envelope from the linear-subclass section.

No fixed-window assumption is used here.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearReducedWitnessBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w} [Fintype N]

/--
Minimum productive yields inherit the short-yield bound supplied by the
linear-spine shape.
-/
theorem minimumCanonicalYield_linear_length_le
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (Wrapper : ActiveTypedSymbol Active → Prop)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Wrapper)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C) :
    ∀ X : N × M,
      Active X →
      (C.omega X).length ≤
        @Fintype.card
          (ActiveTypedSymbol Active)
          (Fintype.ofFinite _) := by
  classical
  letI : Fintype (ActiveTypedSymbol Active) :=
    Fintype.ofFinite _
  intro X hX
  let XT : ActiveTypedSymbol Active := ⟨X, hX⟩
  have dReduced :
      ReducedTypedDerives
        H terminalRule binaryRule Active X (C.omega X) :=
    C.omegaDerives X hX
  have dActiveRaw :=
    reducedTypedDerives_to_activeUntypedDerives
      H terminalRule binaryRule Active dReduced
  have dActive :
      UntypedDerives
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        XT (C.omega X) := by
    simpa [XT] using dActiveRaw
  obtain ⟨word', dword', hlen⟩ :=
    exists_linear_short_yield
      (ActiveTypedTerminalRule H terminalRule Active)
      (ActiveTypedBinaryRule binaryRule Active)
      Wrapper shape dActive
  have dReduced' :
      ReducedTypedDerives
        H terminalRule binaryRule Active X word' := by
    have h :=
      activeUntypedDerives_to_reducedTypedDerives
        H terminalRule binaryRule Active dword'
    simpa [XT] using h
  exact
    le_trans
      (minimal.omega_minimal X hX word' dReduced')
      hlen

/--
Minimum reaching contexts inherit the 2 n_t context bound from the
linear-spine reaching semantics.
-/
theorem minimumCanonicalContext_linear_length_le
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (Wrapper : ActiveTypedSymbol Active → Prop)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Wrapper)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C) :
    ∀ X : N × M,
      Active X →
      (C.left X).length + (C.right X).length ≤
        2 *
          @Fintype.card
            (ActiveTypedSymbol Active)
            (Fintype.ofFinite _) := by
  classical
  letI : Fintype (ActiveTypedSymbol Active) :=
    Fintype.ofFinite _
  letI : DecidableEq (ActiveTypedSymbol Active) :=
    Classical.decEq _
  intro X hX
  let XT : ActiveTypedSymbol Active := ⟨X, hX⟩
  obtain ⟨R, left₀, right₀, path₀, siblings₀,
      hstart, spine₀⟩ :=
    reach.spine XT

  have hshort :
      ∀ (Y : ActiveTypedSymbol Active) {z₀ : Word α},
        ¬ Wrapper Y →
        UntypedDerives
          (ActiveTypedTerminalRule H terminalRule Active)
          (ActiveTypedBinaryRule binaryRule Active)
          Y z₀ →
        ∃ z : Word α,
          UntypedDerives
            (ActiveTypedTerminalRule H terminalRule Active)
            (ActiveTypedBinaryRule binaryRule Active)
            Y z
          ∧ z.length ≤
              Fintype.card (ActiveTypedSymbol Active) := by
    intro Y z₀ hY dY
    exact
      exists_linear_short_yield
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Wrapper shape dY

  obtain ⟨left', right', path', siblings',
      spine', hnodup, hlen⟩ :=
    linearReachingSpine_short_context
      (ActiveTypedTerminalRule H terminalRule Active)
      (ActiveTypedBinaryRule binaryRule Active)
      Wrapper shape hshort spine₀

  have hreach :
      ∀ {z : Word α},
        ReducedTypedDerives
          H terminalRule binaryRule Active X z →
        ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active
          (left' ++ z ++ right') := by
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

  exact
    le_trans
      (minimal.context_minimal X hX left' right' hreach)
      hlen

/--
The two semantic conclusions of the linear short-witness lemma, packaged for
the actual minimum canonical choices.
-/
theorem minimumCanonicalChoices_linear_bounds
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (Wrapper : ActiveTypedSymbol Active → Prop)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Wrapper)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C) :
    (∀ X : N × M,
      Active X →
      (C.omega X).length ≤
        @Fintype.card
          (ActiveTypedSymbol Active)
          (Fintype.ofFinite _))
    ∧
    (∀ X : N × M,
      Active X →
      (C.left X).length + (C.right X).length ≤
        2 *
          @Fintype.card
            (ActiveTypedSymbol Active)
            (Fintype.ofFinite _)) := by
  constructor
  · exact
      minimumCanonicalYield_linear_length_le
        H terminalRule binaryRule startRule epsilonStart
        Active Wrapper shape C minimal
  · exact
      minimumCanonicalContext_linear_length_le
        H terminalRule binaryRule startRule epsilonStart
        Active Wrapper shape reach C minimal

/--
Every actual canonical witness word has the linear length bound once the
reduced typed grammar has the linear-spine shape.
-/
theorem canonicalWitnessFinset_linear_length_le_of_shape
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (Wrapper : ActiveTypedSymbol Active → Prop)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Wrapper)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    {word : Word α}
    (hword :
      word ∈
        canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C) :
    word.length ≤
      linearCanonicalWitnessLengthEnvelope
        (@Fintype.card
          (ActiveTypedSymbol Active)
          (Fintype.ofFinite _)) := by
  have hb :=
    minimumCanonicalChoices_linear_bounds
      H terminalRule binaryRule startRule epsilonStart
      Active Wrapper shape reach C minimal
  exact
    mem_canonicalWitnessFinset_linear_length_le
      H terminalRule binaryRule startRule epsilonStart
      Active C
      (@Fintype.card
        (ActiveTypedSymbol Active)
        (Fintype.ofFinite _))
      hb.1 hb.2 hword

/--
The actual minimum canonical characteristic sample has polynomial encoded
size in the underlying grammar counts for the linear subclass.
-/
theorem canonicalWitnessFinset_linear_norm_le_of_shape
    [Fintype α] [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (Wrapper : ActiveTypedSymbol Active → Prop)
    (shape :
      LinearSpineShape
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        Wrapper)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C) :
    (∑ word ∈
      canonicalWitnessFinset
        H terminalRule binaryRule startRule epsilonStart Active C,
      (word.length + 1))
      ≤
    linearCharacteristicEnvelope
      (Fintype.card M)
      (Fintype.card N)
      (@Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _))
      (@Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _)) := by
  have hb :=
    minimumCanonicalChoices_linear_bounds
      H terminalRule binaryRule startRule epsilonStart
      Active Wrapper shape reach C minimal
  exact
    canonicalWitnessFinset_linear_norm_le
      H terminalRule binaryRule startRule epsilonStart
      Active C hb.1 hb.2

end LinearReducedWitnessBridge

end TCS1
end LeanCfgProject
