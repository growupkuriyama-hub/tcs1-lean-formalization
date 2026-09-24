import LeanCfgProject.TCS1.ReconstructionFactorSlotState
import LeanCfgProject.TCS1.ReconstructionActiveGrammar
import LeanCfgProject.TCS1.BinaryUnitElimination
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage

/-!
# TCS #1 v79: computable factor-slot presentation of reconstruction

This module moves the reconstructed hypothesis from the proof-carrying
`ActiveReconstructionNonterminal K` representation to the genuinely
computable finite two-cut space `ReconstructionFactorSlot K`.

Every rule explicitly requires the decoded slot to be observed.  Hence
reversed/empty slots are inert, while every paper-facing observed symbol has
its canonical slot.  The four non-start reconstruction rules R1--R4 are then
represented exactly as terminal/binary/unit rules on this finite state space.

The main result is a start-language equivalence with `BatchLanguage H K`.
This is the semantic bridge needed before replacing the remaining classical
finite-state enumeration in the specialized CYK wrapper.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ReconstructionFactorSlotGrammar

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]

/-- The decoded paper-facing symbol carried by a factor slot. -/
abbrev reconstructionFactorSlotSymbol
    {K : Finset (Word α)}
    (A : ReconstructionFactorSlot K) :
    ReconstructionNonterminal α :=
  reconstructionFactorSlotNonterminal A

/-- A factor slot is semantically active exactly when its decoded occurrence is observed. -/
def ReconstructionFactorSlotObserved
    (K : Finset (Word α))
    (A : ReconstructionFactorSlot K) : Prop :=
  let q := reconstructionFactorSlotSymbol A
  Observed K q.factor q.leftContext q.rightContext

/--
Finite binary/terminal/unit grammar on the computable factor-slot state type.
The relations mirror R1--R4 after decoding the three stored word components.
-/
def reconstructionFactorSlotGrammar
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    BinaryNullableGrammar
      (ReconstructionFactorSlot K) α where
  terminalRule A a :=
    ReconstructionFactorSlotObserved K A ∧
      (reconstructionFactorSlotSymbol A).factor = [a]
  binaryRule A B C :=
    ReconstructionFactorSlotObserved K A ∧
    ReconstructionFactorSlotObserved K B ∧
    ReconstructionFactorSlotObserved K C ∧
    (reconstructionFactorSlotSymbol A).factor =
      (reconstructionFactorSlotSymbol B).factor ++
        (reconstructionFactorSlotSymbol C).factor ∧
    (reconstructionFactorSlotSymbol B).leftContext =
      (reconstructionFactorSlotSymbol A).leftContext ∧
    (reconstructionFactorSlotSymbol B).rightContext =
      (reconstructionFactorSlotSymbol C).factor ++
        (reconstructionFactorSlotSymbol A).rightContext ∧
    (reconstructionFactorSlotSymbol C).leftContext =
      (reconstructionFactorSlotSymbol A).leftContext ++
        (reconstructionFactorSlotSymbol B).factor ∧
    (reconstructionFactorSlotSymbol C).rightContext =
      (reconstructionFactorSlotSymbol A).rightContext
  epsilonRule _ := False
  unitRule A B :=
    ReconstructionFactorSlotObserved K A ∧
    ReconstructionFactorSlotObserved K B ∧
    ((reconstructionFactorSlotSymbol A).factor =
        (reconstructionFactorSlotSymbol B).factor ∨
      ((reconstructionFactorSlotSymbol A).leftContext =
          (reconstructionFactorSlotSymbol B).leftContext ∧
       (reconstructionFactorSlotSymbol A).rightContext =
          (reconstructionFactorSlotSymbol B).rightContext ∧
       H.h (reconstructionFactorSlotSymbol A).factor =
          H.h (reconstructionFactorSlotSymbol B).factor))

/-- Canonical observed slots are active in the factor-slot grammar. -/
theorem observedReconstructionFactorSlot_isObserved
    (K : Finset (Word α))
    {x u v : Word α}
    (hobs : Observed K x u v) :
    ReconstructionFactorSlotObserved K
      (observedReconstructionFactorSlot K hobs) := by
  have hdecode :=
    reconstructionFactorSlotNonterminal_observed K hobs
  simpa [ReconstructionFactorSlotObserved,
    reconstructionFactorSlotSymbol, hdecode] using hobs

/--
Forward simulation of R1--R4 into the computable factor-slot grammar.
-/
theorem hypDerives_to_factorSlotGrammar
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    BinaryNullableDerives
      (reconstructionFactorSlotGrammar H K)
      (observedReconstructionFactorSlot K
        (hypDerives_root_observed H K d))
      w := by
  induction d with
  | @r4 a u v hobs =>
      apply BinaryNullableDerives.terminal
      constructor
      · exact observedReconstructionFactorSlot_isObserved K hobs
      · have hdecode :=
          reconstructionFactorSlotNonterminal_observed K hobs
        exact congrArg ReconstructionNonterminal.factor hdecode
  | @r3 x x' u v w hobs hobs' htype d ih =>
      apply BinaryNullableDerives.unit
        (B := observedReconstructionFactorSlot K hobs')
      · refine ⟨observedReconstructionFactorSlot_isObserved K hobs,
          observedReconstructionFactorSlot_isObserved K hobs', ?_⟩
        right
        simpa only [reconstructionFactorSlotNonterminal_observed] using
          (show u = u ∧ v = v ∧ H.h x = H.h x' from
            ⟨rfl, rfl, htype⟩)
      · exact ih
  | @r2 x u v u' v' w hobs hobs' d ih =>
      apply BinaryNullableDerives.unit
        (B := observedReconstructionFactorSlot K hobs')
      · refine ⟨observedReconstructionFactorSlot_isObserved K hobs,
          observedReconstructionFactorSlot_isObserved K hobs', ?_⟩
        left
        simpa only [reconstructionFactorSlotNonterminal_observed]
      · exact ih
  | @r1 x y u v w₁ w₂ hparent hleft hright dleft dright ihleft ihrigh =>
      apply BinaryNullableDerives.binary
        (B := observedReconstructionFactorSlot K hleft)
        (C := observedReconstructionFactorSlot K hright)
      · refine ⟨observedReconstructionFactorSlot_isObserved K hparent,
          observedReconstructionFactorSlot_isObserved K hleft,
          observedReconstructionFactorSlot_isObserved K hright, ?_⟩
        simpa only [reconstructionFactorSlotNonterminal_observed] using
          (show
            x ++ y = x ++ y ∧
            u = u ∧
            y ++ v = y ++ v ∧
            u ++ x = u ++ x ∧
            v = v
          from ⟨rfl, rfl, rfl, rfl, rfl⟩)
      · exact ihleft
      · exact ihrigh

/--
Reverse simulation: every derivation of an active factor slot is an R1--R4
derivation of its decoded paper-facing symbol.
-/
theorem factorSlotGrammar_to_hypDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A : ReconstructionFactorSlot K}
    {w : Word α}
    (d :
      BinaryNullableDerives
        (reconstructionFactorSlotGrammar H K)
        A w) :
    HypDerives H K
      (reconstructionFactorSlotSymbol A).factor
      (reconstructionFactorSlotSymbol A).leftContext
      (reconstructionFactorSlotSymbol A).rightContext
      w := by
  induction d with
  | @terminal A a hterm =>
      rcases hterm with ⟨hobs, hfac⟩
      change
        Observed K
          (reconstructionFactorSlotSymbol A).factor
          (reconstructionFactorSlotSymbol A).leftContext
          (reconstructionFactorSlotSymbol A).rightContext
        at hobs
      have hobs' :
          Observed K [a]
            (reconstructionFactorSlotSymbol A).leftContext
            (reconstructionFactorSlotSymbol A).rightContext := by
        simpa [hfac] using hobs
      have h :=
        HypDerives.r4
          (H := H) (K := K) hobs'
      simpa [hfac] using h
  | @epsilon A heps =>
      exact False.elim heps
  | @unit A B w hunit d ih =>
      rcases hunit with ⟨hobsA, hobsB, hrel⟩
      change
        Observed K
          (reconstructionFactorSlotSymbol A).factor
          (reconstructionFactorSlotSymbol A).leftContext
          (reconstructionFactorSlotSymbol A).rightContext
        at hobsA
      change
        Observed K
          (reconstructionFactorSlotSymbol B).factor
          (reconstructionFactorSlotSymbol B).leftContext
          (reconstructionFactorSlotSymbol B).rightContext
        at hobsB
      rcases hrel with hsame | htyped
      · have hobsB' :
            Observed K
              (reconstructionFactorSlotSymbol A).factor
              (reconstructionFactorSlotSymbol B).leftContext
              (reconstructionFactorSlotSymbol B).rightContext := by
          simpa [hsame] using hobsB
        have ih' :
            HypDerives H K
              (reconstructionFactorSlotSymbol A).factor
              (reconstructionFactorSlotSymbol B).leftContext
              (reconstructionFactorSlotSymbol B).rightContext
              w := by
          simpa [hsame] using ih
        exact
          HypDerives.r2
            (H := H) (K := K)
            hobsA hobsB' ih'
      · rcases htyped with ⟨hleft, hright, htype⟩
        have hobsB' :
            Observed K
              (reconstructionFactorSlotSymbol B).factor
              (reconstructionFactorSlotSymbol A).leftContext
              (reconstructionFactorSlotSymbol A).rightContext := by
          simpa [hleft, hright] using hobsB
        have ih' :
            HypDerives H K
              (reconstructionFactorSlotSymbol B).factor
              (reconstructionFactorSlotSymbol A).leftContext
              (reconstructionFactorSlotSymbol A).rightContext
              w := by
          simpa [hleft, hright] using ih
        exact
          HypDerives.r3
            (H := H) (K := K)
            hobsA hobsB' htype ih'
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      rcases hbin with
        ⟨hobsA, hobsB, hobsC,
          hfac, hleftB, hrightB, hleftC, hrightC⟩
      change
        Observed K
          (reconstructionFactorSlotSymbol A).factor
          (reconstructionFactorSlotSymbol A).leftContext
          (reconstructionFactorSlotSymbol A).rightContext
        at hobsA
      change
        Observed K
          (reconstructionFactorSlotSymbol B).factor
          (reconstructionFactorSlotSymbol B).leftContext
          (reconstructionFactorSlotSymbol B).rightContext
        at hobsB
      change
        Observed K
          (reconstructionFactorSlotSymbol C).factor
          (reconstructionFactorSlotSymbol C).leftContext
          (reconstructionFactorSlotSymbol C).rightContext
        at hobsC
      have hleftObs :
          Observed K
            (reconstructionFactorSlotSymbol B).factor
            (reconstructionFactorSlotSymbol A).leftContext
            ((reconstructionFactorSlotSymbol C).factor ++
              (reconstructionFactorSlotSymbol A).rightContext) := by
        simpa [hleftB, hrightB] using hobsB
      have hrightObs :
          Observed K
            (reconstructionFactorSlotSymbol C).factor
            ((reconstructionFactorSlotSymbol A).leftContext ++
              (reconstructionFactorSlotSymbol B).factor)
            (reconstructionFactorSlotSymbol A).rightContext := by
        simpa [hleftC, hrightC] using hobsC
      have ihB' :
          HypDerives H K
            (reconstructionFactorSlotSymbol B).factor
            (reconstructionFactorSlotSymbol A).leftContext
            ((reconstructionFactorSlotSymbol C).factor ++
              (reconstructionFactorSlotSymbol A).rightContext)
            wB := by
        simpa [hleftB, hrightB] using ihB
      have ihC' :
          HypDerives H K
            (reconstructionFactorSlotSymbol C).factor
            ((reconstructionFactorSlotSymbol A).leftContext ++
              (reconstructionFactorSlotSymbol B).factor)
            (reconstructionFactorSlotSymbol A).rightContext
            wC := by
        simpa [hleftC, hrightC] using ihC
      have hparent :
          Observed K
            ((reconstructionFactorSlotSymbol B).factor ++
              (reconstructionFactorSlotSymbol C).factor)
            (reconstructionFactorSlotSymbol A).leftContext
            (reconstructionFactorSlotSymbol A).rightContext := by
        simpa [hfac] using hobsA
      have h :=
        HypDerives.r1
          (H := H) (K := K)
          hparent hleftObs hrightObs ihB' ihC'
      simpa [hfac] using h

/-- Start children are observed slots with empty outer contexts. -/
def reconstructionFactorSlotStartRule
    (K : Finset (Word α)) :
    ReconstructionFactorSlot K → Prop :=
  fun A =>
    ReconstructionFactorSlotObserved K A ∧
    (reconstructionFactorSlotSymbol A).leftContext = [] ∧
    (reconstructionFactorSlotSymbol A).rightContext = []

/--
Exact start-language equivalence before unit elimination.
-/
theorem reconstructionFactorSlotStartDerives_iff_batchDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) :
    ((
      ∃ A : ReconstructionFactorSlot K,
        reconstructionFactorSlotStartRule K A ∧
        BinaryNullableDerives
          (reconstructionFactorSlotGrammar H K)
          A w) ∨
      (w = [] ∧ ([] : Word α) ∈ K))
      ↔
    BatchDerives H K w := by
  constructor
  · intro h
    rcases h with hnonempty | heps
    · rcases hnonempty with ⟨A, hstart, hder⟩
      rcases hstart with ⟨hobs, hleft, hright⟩
      have hhyp :=
        factorSlotGrammar_to_hypDerives H K hder
      have hfactorK :
          (reconstructionFactorSlotSymbol A).factor ∈ K := by
        simpa [hleft, hright] using hobs.2
      exact
        BatchDerives.nonempty
          hfactorK hobs.1
          (by simpa [hleft, hright] using hhyp)
    · rcases heps with ⟨rfl, heps⟩
      exact BatchDerives.epsilon heps
  · intro h
    cases h with
    | @nonempty s word hs hsne hder =>
        have hobs : Observed K s [] [] := by
          exact ⟨hsne, by simpa using hs⟩
        left
        refine
          ⟨observedReconstructionFactorSlot K hobs, ?_, ?_⟩
        · refine
            ⟨observedReconstructionFactorSlot_isObserved K hobs, ?_, ?_⟩
          · have hdecode :=
              reconstructionFactorSlotNonterminal_observed K hobs
            exact congrArg ReconstructionNonterminal.leftContext hdecode
          · have hdecode :=
              reconstructionFactorSlotNonterminal_observed K hobs
            exact congrArg ReconstructionNonterminal.rightContext hdecode
        · exact hypDerives_to_factorSlotGrammar H K hder
    | epsilon heps =>
        exact Or.inr ⟨rfl, heps⟩

end ReconstructionFactorSlotGrammar

end TCS1
end LeanCfgProject
