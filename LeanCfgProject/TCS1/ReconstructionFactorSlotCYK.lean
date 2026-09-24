import LeanCfgProject.TCS1.ReconstructionFactorSlotGrammar
import LeanCfgProject.TCS1.FiniteUnitReachability
import LeanCfgProject.TCS1.BinaryMembershipDecision
import LeanCfgProject.TCS1.ConservativeMembershipCost

/-!
# TCS #1 v79: executable factor-slot CYK reconstruction learner

The previous reconstruction-to-CYK bridge used the proof-carrying subtype of
observed paper-facing nonterminals and therefore chose its finite enumeration
classically.  This module replaces that last representation boundary by the
concrete two-cut occurrence space `ReconstructionFactorSlot K`.

The state type is computably finite.  R2/R3 are eliminated by the verified
finite unit-closure machinery, and the resulting terminal/binary grammar is
fed directly to the executable CYK chart.

Under decidable equality on the fixed finite monoid, the final Boolean
membership test below is an ordinary computable definition (not
`noncomputable`) and accepts exactly `BatchLanguage H K`.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ReconstructionFactorSlotCYK

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]
variable [DecidableEq M]

/-- Decidability of observed decoded factor slots. -/
instance instDecidableReconstructionFactorSlotObserved
    (K : Finset (Word α)) :
    DecidablePred (ReconstructionFactorSlotObserved K) := by
  intro A
  unfold ReconstructionFactorSlotObserved
  dsimp only [reconstructionFactorSlotSymbol]
  unfold Observed
  infer_instance

/-- The factor-slot terminal relation is decidable. -/
instance instDecidableReconstructionFactorSlotTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    DecidableRel
      (reconstructionFactorSlotGrammar H K).terminalRule := by
  intro A a
  change
    Decidable
      (ReconstructionFactorSlotObserved K A ∧
        (reconstructionFactorSlotSymbol A).factor = [a])
  infer_instance

/-- The factor-slot binary relation is decidable. -/
instance instDecidableReconstructionFactorSlotBinaryRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ∀ A B : ReconstructionFactorSlot K,
      DecidablePred
        ((reconstructionFactorSlotGrammar H K).binaryRule A B) := by
  intro A B C
  change Decidable
    (ReconstructionFactorSlotObserved K A ∧
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
       (reconstructionFactorSlotSymbol A).rightContext)
  infer_instance

/-- The factor-slot unary relation R2/R3 is decidable. -/
instance instDecidableReconstructionFactorSlotUnitRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    DecidableRel
      (reconstructionFactorSlotGrammar H K).unitRule := by
  intro A B
  change Decidable
    (ReconstructionFactorSlotObserved K A ∧
     ReconstructionFactorSlotObserved K B ∧
     ((reconstructionFactorSlotSymbol A).factor =
        (reconstructionFactorSlotSymbol B).factor ∨
      ((reconstructionFactorSlotSymbol A).leftContext =
          (reconstructionFactorSlotSymbol B).leftContext ∧
       (reconstructionFactorSlotSymbol A).rightContext =
          (reconstructionFactorSlotSymbol B).rightContext ∧
       H.h (reconstructionFactorSlotSymbol A).factor =
          H.h (reconstructionFactorSlotSymbol B).factor)))
  infer_instance

/-- The factor-slot start-child relation is decidable. -/
instance instDecidableReconstructionFactorSlotStartRule
    (K : Finset (Word α)) :
    DecidablePred (reconstructionFactorSlotStartRule K) := by
  intro A
  unfold reconstructionFactorSlotStartRule
  infer_instance

/-- Terminal relation obtained by closing the original R2/R3 unit graph. -/
def reconstructionFactorSlotUnitFreeTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ReconstructionFactorSlot K → α → Prop :=
  fun A a =>
    ∃ B : ReconstructionFactorSlot K,
      UnitReach
        (reconstructionFactorSlotGrammar H K).unitRule
        A B ∧
      (reconstructionFactorSlotGrammar H K).terminalRule B a

/-- Binary relation obtained by the same direct R2/R3 unit closure. -/
def reconstructionFactorSlotUnitFreeBinaryRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ReconstructionFactorSlot K →
      ReconstructionFactorSlot K →
      ReconstructionFactorSlot K → Prop :=
  fun A C D =>
    ∃ B : ReconstructionFactorSlot K,
      UnitReach
        (reconstructionFactorSlotGrammar H K).unitRule
        A B ∧
      (reconstructionFactorSlotGrammar H K).binaryRule B C D

/--
The finite unit-free terminal relation is decidable by the executable
finite-graph closure of the original R2/R3 relation.
-/
instance instDecidableReconstructionFactorSlotUnitFreeTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    DecidableRel
      (reconstructionFactorSlotUnitFreeTerminalRule H K) := by
  intro A a
  unfold reconstructionFactorSlotUnitFreeTerminalRule
  infer_instance

/-- The copied binary relation is decidable by the same finite closure. -/
instance instDecidableReconstructionFactorSlotUnitFreeBinaryRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ∀ A C : ReconstructionFactorSlot K,
      DecidablePred
        (reconstructionFactorSlotUnitFreeBinaryRule H K A C) := by
  intro A C D
  unfold reconstructionFactorSlotUnitFreeBinaryRule
  infer_instance

/-- Lift an original derivation backward along an R2/R3 unit-closure path. -/
theorem factorSlotGrammarDerives_of_unitReach
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A B : ReconstructionFactorSlot K}
    {w : Word α}
    (hAB :
      UnitReach
        (reconstructionFactorSlotGrammar H K).unitRule
        A B)
    (d :
      BinaryNullableDerives
        (reconstructionFactorSlotGrammar H K)
        B w) :
    BinaryNullableDerives
      (reconstructionFactorSlotGrammar H K)
      A w := by
  induction hAB with
  | refl _ =>
      exact d
  | @step A B C hAB hBC ih =>
      exact
        BinaryNullableDerives.unit
          hAB (ih d)

/--
Changing the root backward along an R2/R3 closure path is admissible in the
direct copied terminal/binary grammar.
-/
theorem factorSlotUnitFreeUntyped_of_unitReach
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A B : ReconstructionFactorSlot K}
    {w : Word α}
    (hAB :
      UnitReach
        (reconstructionFactorSlotGrammar H K).unitRule
        A B)
    (d :
      UntypedDerives
        (reconstructionFactorSlotUnitFreeTerminalRule H K)
        (reconstructionFactorSlotUnitFreeBinaryRule H K)
        B w) :
    UntypedDerives
      (reconstructionFactorSlotUnitFreeTerminalRule H K)
      (reconstructionFactorSlotUnitFreeBinaryRule H K)
      A w := by
  induction d with
  | @terminal B a hterm =>
      rcases hterm with ⟨C, hBC, hCa⟩
      exact
        UntypedDerives.terminal
          ⟨C, UnitReach.trans hAB hBC, hCa⟩
  | @binary B C D wC wD hbin dC dD ihC ihD =>
      rcases hbin with ⟨E, hBE, hECD⟩
      exact
        UntypedDerives.binary
          ⟨E, UnitReach.trans hAB hBE, hECD⟩
          dC dD

/--
Forward direct unit elimination for the factor-slot grammar.  There are no
epsilon rules, so only R2/R3 unit edges need to be collapsed.
-/
theorem factorSlotGrammar_to_unitFreeUntyped
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A : ReconstructionFactorSlot K}
    {w : Word α}
    (d :
      BinaryNullableDerives
        (reconstructionFactorSlotGrammar H K)
        A w) :
    UntypedDerives
      (reconstructionFactorSlotUnitFreeTerminalRule H K)
      (reconstructionFactorSlotUnitFreeBinaryRule H K)
      A w := by
  induction d with
  | @terminal A a h =>
      exact
        UntypedDerives.terminal
          ⟨A, UnitReach.refl A, h⟩
  | @epsilon A h =>
      exact False.elim h
  | @unit A B w h d ih =>
      exact
        factorSlotUnitFreeUntyped_of_unitReach
          H K (UnitReach.single h) ih
  | @binary A B C wB wC h dB dC ihB ihC =>
      exact
        UntypedDerives.binary
          ⟨A, UnitReach.refl A, h⟩
          ihB ihC

/-- Reverse expansion of the copied terminal/binary rules. -/
theorem factorSlotUnitFreeUntyped_to_grammar
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A : ReconstructionFactorSlot K}
    {w : Word α}
    (d :
      UntypedDerives
        (reconstructionFactorSlotUnitFreeTerminalRule H K)
        (reconstructionFactorSlotUnitFreeBinaryRule H K)
        A w) :
    BinaryNullableDerives
      (reconstructionFactorSlotGrammar H K)
      A w := by
  induction d with
  | @terminal A a h =>
      rcases h with ⟨B, hAB, hBa⟩
      exact
        factorSlotGrammarDerives_of_unitReach
          H K hAB
          (BinaryNullableDerives.terminal hBa)
  | @binary A C D wC wD h dC dD ihC ihD =>
      rcases h with ⟨B, hAB, hBCD⟩
      have dB :
          BinaryNullableDerives
            (reconstructionFactorSlotGrammar H K)
            B (wC ++ wD) :=
        BinaryNullableDerives.binary
          hBCD ihC ihD
      exact
        factorSlotGrammarDerives_of_unitReach
          H K hAB dB

/--
Exact start-language identity for the fully finite, direct-unit-closed
factor-slot presentation.
-/
theorem reconstructionFactorSlotUnitFree_untypedStartLanguage_eq_batchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    UntypedStartLanguage
        (reconstructionFactorSlotUnitFreeTerminalRule H K)
        (reconstructionFactorSlotUnitFreeBinaryRule H K)
        (reconstructionFactorSlotStartRule K)
        (([] : Word α) ∈ K)
      =
    BatchLanguage H K := by
  apply Set.ext
  intro w
  constructor
  · intro h
    cases h with
    | @nonempty A _ hstart hder =>
        rcases hstart with ⟨hobs, hleft, hright⟩
        change
          Observed K
            (reconstructionFactorSlotSymbol A).factor
            (reconstructionFactorSlotSymbol A).leftContext
            (reconstructionFactorSlotSymbol A).rightContext
          at hobs
        have dBin :
            BinaryNullableDerives
              (reconstructionFactorSlotGrammar H K)
              A w :=
          factorSlotUnitFreeUntyped_to_grammar
            H K hder
        have hhyp :=
          factorSlotGrammar_to_hypDerives H K dBin
        have hs :
            (reconstructionFactorSlotSymbol A).factor ∈ K := by
          simpa [hleft, hright] using hobs.2
        exact
          BatchDerives.nonempty
            hs hobs.1
            (by simpa [hleft, hright] using hhyp)
    | epsilon heps =>
        exact BatchDerives.epsilon heps
  · intro h
    cases h with
    | @nonempty s _ hs hsne hder =>
        have hobs : Observed K s [] [] := by
          exact ⟨hsne, by simpa using hs⟩
        let A : ReconstructionFactorSlot K :=
          observedReconstructionFactorSlot K hobs
        have dBin :
            BinaryNullableDerives
              (reconstructionFactorSlotGrammar H K)
              A w := by
          simpa [A] using
            (hypDerives_to_factorSlotGrammar H K hder)
        have hstart :
            reconstructionFactorSlotStartRule K A := by
          refine
            ⟨observedReconstructionFactorSlot_isObserved K hobs, ?_, ?_⟩
          · have hdecode :=
              reconstructionFactorSlotNonterminal_observed K hobs
            exact congrArg ReconstructionNonterminal.leftContext hdecode
          · have hdecode :=
              reconstructionFactorSlotNonterminal_observed K hobs
            exact congrArg ReconstructionNonterminal.rightContext hdecode
        exact
          UntypedStartDerives.nonempty
            hstart
            (factorSlotGrammar_to_unitFreeUntyped
              H K dBin)
    | epsilon heps =>
        exact UntypedStartDerives.epsilon heps

/--
Fully executable CYK Boolean test for the actual reconstructed hypothesis.
No `noncomputable` wrapper remains.
-/
def reconstructionFactorSlotCYKMember
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) : Bool :=
  cykStartMember
    (reconstructionFactorSlotUnitFreeTerminalRule H K)
    (reconstructionFactorSlotUnitFreeBinaryRule H K)
    (reconstructionFactorSlotStartRule K)
    (([] : Word α) ∈ K)
    w

/-- Exact correctness of the fully executable reconstructed-hypothesis parser. -/
theorem reconstructionFactorSlotCYKMember_eq_true_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) :
    reconstructionFactorSlotCYKMember H K w = true
      ↔
    w ∈ BatchLanguage H K := by
  rw [reconstructionFactorSlotCYKMember]
  rw [cykStartMember_eq_true_iff]
  rw [reconstructionFactorSlotUnitFree_untypedStartLanguage_eq_batchLanguage]

/--
The exact finite state count consumed by this executable parser is the
two-cut factor-slot cardinality already used in the conservative cost bridge.
-/
theorem reconstructionFactorSlotCYK_conservativeComparison_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    cykNaiveComparisonEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (concreteConservativeHypothesis H datum n)))
        (datum (n + 1)).length
      ≤
    conservativeCYKPrefixEnvelope
      (positiveDataPrefixNorm datum (n + 1)) :=
  concreteConservative_occurrenceIndexed_membershipComparison_le_prefix
    H datum n

/-- All-source unit-closure precomputation has the explicit quartic scan count. -/
def reconstructionUnitClosureTableScanEnvelope
    (stateCount : Nat) : Nat :=
  stateCount * finiteUnitReachScanEnvelope stateCount

theorem reconstructionUnitClosureTableScanEnvelope_eq
    (m : Nat) :
    reconstructionUnitClosureTableScanEnvelope m = m ^ 4 := by
  unfold reconstructionUnitClosureTableScanEnvelope
  rw [finiteUnitReachScanEnvelope_eq]
  ring


/-- The all-source unit-closure scan envelope is monotone in the state count. -/
theorem reconstructionUnitClosureTableScanEnvelope_mono
    {m m' : Nat}
    (h : m ≤ m') :
    reconstructionUnitClosureTableScanEnvelope m ≤
      reconstructionUnitClosureTableScanEnvelope m' := by
  rw [reconstructionUnitClosureTableScanEnvelope_eq,
    reconstructionUnitClosureTableScanEnvelope_eq]
  gcongr

/--
The actual computable factor-slot state count of the current hypothesis is
bounded by the same degree-five prefix envelope used by the reconstruction
size certificate.
-/
theorem reconstructionFactorSlot_current_card_le_prefix_degreeFive
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    Fintype.card
        (ReconstructionFactorSlot
          (concreteConservativeHypothesis H datum n))
      ≤
    5 * (positiveDataPrefixNorm datum (n + 1) + 1) ^ 5 := by
  exact le_trans
    (reconstructionFactorSlot_card_le_outputEncodingEnvelope
      (concreteConservativeHypothesis H datum n))
    (concreteConservative_update_size_certificate
      H datum n).2.1

/--
Prefix-only budget for an executable conservative update, including one
all-source R2/R3 unit-closure precomputation, the CYK membership test, and a
possible reconstruction.
-/
def conservativeExecutableUpdateWorkEnvelope
    (prefixNorm : Nat) : Nat :=
  reconstructionUnitClosureTableScanEnvelope
      (5 * (prefixNorm + 1) ^ 5)
    +
  conservativeUpdateWorkEnvelope prefixNorm

/-- The executable-update envelope is a manifest polynomial expression. -/
theorem conservativeExecutableUpdateWorkEnvelope_polynomial_form
    (p : Nat) :
    conservativeExecutableUpdateWorkEnvelope p =
      (5 * (p + 1) ^ 5) ^ 4 +
        conservativeCYKPrefixEnvelope p +
        5 * (p + 1) ^ 5 := by
  unfold conservativeExecutableUpdateWorkEnvelope
  unfold conservativeUpdateWorkEnvelope
  rw [reconstructionUnitClosureTableScanEnvelope_eq]
  ring

/--
End-to-end cost composition for the computable factor-slot parser:
unit closure + CYK membership + a possible rebuild are bounded by one explicit
polynomial in the positive-data prefix.
-/
theorem concreteConservative_executable_update_work_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    reconstructionUnitClosureTableScanEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (concreteConservativeHypothesis H datum n)))
      +
    (cykNaiveComparisonEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (concreteConservativeHypothesis H datum n)))
        (datum (n + 1)).length
      +
     reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm
          (concreteAccumulatedSample datum (n + 1))))
      ≤
    conservativeExecutableUpdateWorkEnvelope
      (positiveDataPrefixNorm datum (n + 1)) := by
  have hcard :=
    reconstructionFactorSlot_current_card_le_prefix_degreeFive
      H datum n
  have hclosure :=
    reconstructionUnitClosureTableScanEnvelope_mono hcard
  have hwork :=
    concreteConservative_occurrenceIndexed_update_work_le_prefix
      H datum n
  unfold conservativeExecutableUpdateWorkEnvelope
  exact Nat.add_le_add hclosure hwork

end ReconstructionFactorSlotCYK

end TCS1
end LeanCfgProject
