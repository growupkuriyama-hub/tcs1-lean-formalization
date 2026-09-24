import LeanCfgProject.TCS1.FixedWindowReducedContextFacade

/-!
# TCS #1 v68: typed reachability to reaching-spine bridge

The reduced typed grammar keeps a finite set of active typed symbols.  Its
ordinary reachability proof follows active binary-rule child edges starting
from a non-start child of a start rule.  Lemma 7.2 needs the same information
as an explicit `ReachingSpine`, with terminal yields for every off-path
sibling.

Productivity is already packaged by `ReducedWitnessChoices`: every active
typed symbol has the canonical yield `omega`.  This file therefore converts
ordinary active-symbol reachability into the structural spine certificate used
by `FixedWindowReducedContextFacade`.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section ActiveTypedReachabilityBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Reachability through active typed binary-rule child edges. -/
inductive ActiveTypedReachable
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (Active : N × M → Prop) :
    ActiveTypedSymbol Active → Prop
  | start
      {R : ActiveTypedSymbol Active}
      (hstart : startRule R.1.1) :
      ActiveTypedReachable binaryRule startRule Active R
  | left
      {A B C : ActiveTypedSymbol Active}
      (hA :
        ActiveTypedReachable
          binaryRule startRule Active A)
      (hbin :
        ActiveTypedBinaryRule binaryRule Active
          A B C) :
      ActiveTypedReachable
        binaryRule startRule Active B
  | right
      {A B C : ActiveTypedSymbol Active}
      (hA :
        ActiveTypedReachable
          binaryRule startRule Active A)
      (hbin :
        ActiveTypedBinaryRule binaryRule Active
          A B C) :
      ActiveTypedReachable
        binaryRule startRule Active C

/--
One active-symbol reachability proof yields an explicit reaching spine.

At each child edge the sibling is expanded by its canonical productive yield,
then the one-edge spine is composed with the already constructed prefix.
-/
theorem activeTypedReachable_to_reachingSpine
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (choices :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    {X : ActiveTypedSymbol Active}
    (hreach :
      ActiveTypedReachable
        binaryRule startRule Active X) :
    ∃ R : ActiveTypedSymbol Active,
      ∃ left right : Word α,
        ∃ path : List (ActiveTypedSymbol Active),
          ∃ siblings : List Nat,
            startRule R.1.1
            ∧
            ReachingSpine
              (ActiveTypedTerminalRule H terminalRule Active)
              (ActiveTypedBinaryRule binaryRule Active)
              R X left right path siblings := by
  induction hreach with
  | @start R hstart =>
      exact
        ⟨R, [], [], [R], [], hstart,
          ReachingSpine.hole⟩

  | @left A B C hA hbin ih =>
      obtain ⟨R, left₀, right₀, path₀, siblings₀,
          hstart, outer⟩ := ih

      have dCReduced :
          ReducedTypedDerives
            H terminalRule binaryRule Active
            C.1 (choices.omega C.1) :=
        choices.omegaDerives C.1 C.2

      have dCActiveRaw :=
        reducedTypedDerives_to_activeUntypedDerives
          H terminalRule binaryRule Active dCReduced

      have dCActive :
          UntypedDerives
            (ActiveTypedTerminalRule H terminalRule Active)
            (ActiveTypedBinaryRule binaryRule Active)
            C (choices.omega C.1) := by
        simpa using dCActiveRaw

      have one :
          ReachingSpine
            (ActiveTypedTerminalRule H terminalRule Active)
            (ActiveTypedBinaryRule binaryRule Active)
            A B
            []
            (choices.omega C.1)
            [A, B]
            [(choices.omega C.1).length] := by
        simpa using
          (ReachingSpine.binaryLeft
            hbin
            (ReachingSpine.hole :
              ReachingSpine
                (ActiveTypedTerminalRule H terminalRule Active)
                (ActiveTypedBinaryRule binaryRule Active)
                B B [] [] [B] [])
            dCActive)

      obtain ⟨path', siblings', composed⟩ :=
        exists_reachingSpine_compose
          (ActiveTypedTerminalRule H terminalRule Active)
          (ActiveTypedBinaryRule binaryRule Active)
          outer one

      exact
        ⟨R,
          left₀ ++ [],
          (choices.omega C.1) ++ right₀,
          path', siblings',
          hstart, composed⟩

  | @right A B C hA hbin ih =>
      obtain ⟨R, left₀, right₀, path₀, siblings₀,
          hstart, outer⟩ := ih

      have dBReduced :
          ReducedTypedDerives
            H terminalRule binaryRule Active
            B.1 (choices.omega B.1) :=
        choices.omegaDerives B.1 B.2

      have dBActiveRaw :=
        reducedTypedDerives_to_activeUntypedDerives
          H terminalRule binaryRule Active dBReduced

      have dBActive :
          UntypedDerives
            (ActiveTypedTerminalRule H terminalRule Active)
            (ActiveTypedBinaryRule binaryRule Active)
            B (choices.omega B.1) := by
        simpa using dBActiveRaw

      have one :
          ReachingSpine
            (ActiveTypedTerminalRule H terminalRule Active)
            (ActiveTypedBinaryRule binaryRule Active)
            A C
            (choices.omega B.1)
            []
            [A, C]
            [(choices.omega B.1).length] := by
        simpa using
          (ReachingSpine.binaryRight
            hbin
            dBActive
            (ReachingSpine.hole :
              ReachingSpine
                (ActiveTypedTerminalRule H terminalRule Active)
                (ActiveTypedBinaryRule binaryRule Active)
                C C [] [] [C] []))

      obtain ⟨path', siblings', composed⟩ :=
        exists_reachingSpine_compose
          (ActiveTypedTerminalRule H terminalRule Active)
          (ActiveTypedBinaryRule binaryRule Active)
          outer one

      exact
        ⟨R,
          left₀ ++ choices.omega B.1,
          [] ++ right₀,
          path', siblings',
          hstart, composed⟩

/--
If every active typed symbol is reachable by active child edges, the structural
reachability interface required by Lemma 7.2 follows automatically.
-/
theorem activeTypedStructuralReachability_of_reachable
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (choices :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (hreaches :
      ∀ X : ActiveTypedSymbol Active,
        ActiveTypedReachable
          binaryRule startRule Active X) :
    ActiveTypedStructuralReachability
      H terminalRule binaryRule startRule Active where
  spine := by
    intro X
    exact
      activeTypedReachable_to_reachingSpine
        H terminalRule binaryRule startRule epsilonStart
        Active choices (hreaches X)

end ActiveTypedReachabilityBridge

end TCS1
end LeanCfgProject
