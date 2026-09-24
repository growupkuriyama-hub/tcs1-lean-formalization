import LeanCfgProject.TCS1.ReconstructionFactorSlotCYK

/-!
# TCS #1 v79: materialized finite production tables

The executable reconstruction learner already uses a computable finite
factor-slot state space and decidable rule predicates.  This module lowers the
representation one step further: under the manuscript's finite-alphabet
setting, the relevant productions are stored explicitly as finite tables.

We materialize both the original R1--R4 presentation and the direct
unit-closed terminal/binary presentation consumed by CYK.  Membership in each
table is proved equivalent to the corresponding semantic rule predicate, and
a second CYK wrapper is defined directly from table membership.

This is representation-level strengthening: it does not change the language
or learner, but records that the parser can consume concrete finite production
data rather than opaque decidable predicates.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ReconstructionProductionTables

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [Fintype α] [DecidableEq α]
variable [DecidableEq M]

abbrev ReconstructionFactorSlotBinaryEntry
    (K : Finset (Word α)) :=
  ReconstructionFactorSlot K ×
    (ReconstructionFactorSlot K × ReconstructionFactorSlot K)

/-- Explicit terminal-production table for the original R1--R4 grammar. -/
def reconstructionFactorSlotTerminalTable
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Finset (ReconstructionFactorSlot K × α) :=
  Finset.univ.filter
    (fun p =>
      (reconstructionFactorSlotGrammar H K).terminalRule
        p.1 p.2)

/-- Explicit binary-production table for original R1. -/
def reconstructionFactorSlotBinaryTable
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Finset (ReconstructionFactorSlotBinaryEntry K) :=
  Finset.univ.filter
    (fun p =>
      (reconstructionFactorSlotGrammar H K).binaryRule
        p.1 p.2.1 p.2.2)

/-- Explicit unary-production table for original R2/R3. -/
def reconstructionFactorSlotUnitTable
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Finset (ReconstructionFactorSlot K × ReconstructionFactorSlot K) :=
  Finset.univ.filter
    (fun p =>
      (reconstructionFactorSlotGrammar H K).unitRule
        p.1 p.2)

/-- Explicit set of separated-start children. -/
def reconstructionFactorSlotStartTable
    (K : Finset (Word α)) :
    Finset (ReconstructionFactorSlot K) :=
  Finset.univ.filter
    (reconstructionFactorSlotStartRule K)

@[simp] theorem mem_reconstructionFactorSlotTerminalTable_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A : ReconstructionFactorSlot K)
    (a : α) :
    (A, a) ∈ reconstructionFactorSlotTerminalTable H K
      ↔
    (reconstructionFactorSlotGrammar H K).terminalRule A a := by
  simp [reconstructionFactorSlotTerminalTable]

@[simp] theorem mem_reconstructionFactorSlotBinaryTable_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A B C : ReconstructionFactorSlot K) :
    (A, (B, C)) ∈ reconstructionFactorSlotBinaryTable H K
      ↔
    (reconstructionFactorSlotGrammar H K).binaryRule A B C := by
  simp [reconstructionFactorSlotBinaryTable]

@[simp] theorem mem_reconstructionFactorSlotUnitTable_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A B : ReconstructionFactorSlot K) :
    (A, B) ∈ reconstructionFactorSlotUnitTable H K
      ↔
    (reconstructionFactorSlotGrammar H K).unitRule A B := by
  simp [reconstructionFactorSlotUnitTable]

@[simp] theorem mem_reconstructionFactorSlotStartTable_iff
    (K : Finset (Word α))
    (A : ReconstructionFactorSlot K) :
    A ∈ reconstructionFactorSlotStartTable K
      ↔
    reconstructionFactorSlotStartRule K A := by
  simp [reconstructionFactorSlotStartTable]

/-- Materialized direct-unit-closed terminal table consumed by CYK. -/
def reconstructionFactorSlotUnitFreeTerminalTable
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Finset (ReconstructionFactorSlot K × α) :=
  Finset.univ.filter
    (fun p =>
      reconstructionFactorSlotUnitFreeTerminalRule H K
        p.1 p.2)

/-- Materialized direct-unit-closed binary table consumed by CYK. -/
def reconstructionFactorSlotUnitFreeBinaryTable
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Finset (ReconstructionFactorSlotBinaryEntry K) :=
  Finset.univ.filter
    (fun p =>
      reconstructionFactorSlotUnitFreeBinaryRule H K
        p.1 p.2.1 p.2.2)

@[simp] theorem mem_reconstructionFactorSlotUnitFreeTerminalTable_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A : ReconstructionFactorSlot K)
    (a : α) :
    (A, a) ∈
        reconstructionFactorSlotUnitFreeTerminalTable H K
      ↔
    reconstructionFactorSlotUnitFreeTerminalRule H K A a := by
  simp [reconstructionFactorSlotUnitFreeTerminalTable]

@[simp] theorem mem_reconstructionFactorSlotUnitFreeBinaryTable_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A B C : ReconstructionFactorSlot K) :
    (A, (B, C)) ∈
        reconstructionFactorSlotUnitFreeBinaryTable H K
      ↔
    reconstructionFactorSlotUnitFreeBinaryRule H K A B C := by
  simp [reconstructionFactorSlotUnitFreeBinaryTable]

/-- Table-membership terminal predicate. -/
def reconstructionMaterializedTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ReconstructionFactorSlot K → α → Prop :=
  fun A a =>
    (A, a) ∈
      reconstructionFactorSlotUnitFreeTerminalTable H K

/-- Table-membership binary predicate. -/
def reconstructionMaterializedBinaryRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ReconstructionFactorSlot K →
      ReconstructionFactorSlot K →
      ReconstructionFactorSlot K → Prop :=
  fun A B C =>
    (A, (B, C)) ∈
      reconstructionFactorSlotUnitFreeBinaryTable H K

/-- Table-membership start predicate. -/
def reconstructionMaterializedStartRule
    (K : Finset (Word α)) :
    ReconstructionFactorSlot K → Prop :=
  fun A => A ∈ reconstructionFactorSlotStartTable K

@[simp] theorem reconstructionMaterializedTerminalRule_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A : ReconstructionFactorSlot K)
    (a : α) :
    reconstructionMaterializedTerminalRule H K A a
      ↔
    reconstructionFactorSlotUnitFreeTerminalRule H K A a := by
  simp [reconstructionMaterializedTerminalRule]

@[simp] theorem reconstructionMaterializedBinaryRule_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A B C : ReconstructionFactorSlot K) :
    reconstructionMaterializedBinaryRule H K A B C
      ↔
    reconstructionFactorSlotUnitFreeBinaryRule H K A B C := by
  simp [reconstructionMaterializedBinaryRule]

@[simp] theorem reconstructionMaterializedStartRule_iff
    (K : Finset (Word α))
    (A : ReconstructionFactorSlot K) :
    reconstructionMaterializedStartRule K A
      ↔
    reconstructionFactorSlotStartRule K A := by
  simp [reconstructionMaterializedStartRule]


/-- Decidable table lookup for materialized terminal productions. -/
instance instDecidableReconstructionMaterializedTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    DecidableRel (reconstructionMaterializedTerminalRule H K) := by
  intro A a
  unfold reconstructionMaterializedTerminalRule
  infer_instance

/-- Decidable table lookup for materialized binary productions. -/
instance instDecidableReconstructionMaterializedBinaryRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ∀ A B : ReconstructionFactorSlot K,
      DecidablePred (reconstructionMaterializedBinaryRule H K A B) := by
  intro A B C
  exact
    decidable_of_iff
      (reconstructionFactorSlotUnitFreeBinaryRule H K A B C)
      (reconstructionMaterializedBinaryRule_iff H K A B C).symm

/-- Decidable table lookup for materialized start children. -/
instance instDecidableReconstructionMaterializedStartRule
    (K : Finset (Word α)) :
    DecidablePred (reconstructionMaterializedStartRule K) := by
  intro A
  unfold reconstructionMaterializedStartRule
  infer_instance

/-- Concrete table size is bounded by the full state/terminal product. -/
theorem reconstructionFactorSlotUnitFreeTerminalTable_card_le
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    (reconstructionFactorSlotUnitFreeTerminalTable H K).card
      ≤
    Fintype.card (ReconstructionFactorSlot K) *
      Fintype.card α := by
  have h :=
    Finset.card_le_univ
      (reconstructionFactorSlotUnitFreeTerminalTable H K)
  simpa [Fintype.card_prod] using h

/-- Concrete binary table size is bounded by the full cubic state product. -/
theorem reconstructionFactorSlotUnitFreeBinaryTable_card_le
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    (reconstructionFactorSlotUnitFreeBinaryTable H K).card
      ≤
    Fintype.card (ReconstructionFactorSlot K) *
      (Fintype.card (ReconstructionFactorSlot K) *
        Fintype.card (ReconstructionFactorSlot K)) := by
  have h :=
    Finset.card_le_univ
      (reconstructionFactorSlotUnitFreeBinaryTable H K)
  simpa [ReconstructionFactorSlotBinaryEntry,
    Fintype.card_prod] using h

/-- Concrete unit table size is bounded by the full quadratic state product. -/
theorem reconstructionFactorSlotUnitTable_card_le
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    (reconstructionFactorSlotUnitTable H K).card
      ≤
    Fintype.card (ReconstructionFactorSlot K) *
      Fintype.card (ReconstructionFactorSlot K) := by
  have h :=
    Finset.card_le_univ
      (reconstructionFactorSlotUnitTable H K)
  simpa [Fintype.card_prod] using h

/-- Explicit CYK wrapper whose rules are finite-table membership lookups. -/
def reconstructionMaterializedCYKMember
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) : Bool :=
  cykStartMember
    (reconstructionMaterializedTerminalRule H K)
    (reconstructionMaterializedBinaryRule H K)
    (reconstructionMaterializedStartRule K)
    (([] : Word α) ∈ K)
    w

/-- The materialized-table parser accepts exactly the reconstructed language. -/
theorem reconstructionMaterializedCYKMember_eq_true_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) :
    reconstructionMaterializedCYKMember H K w = true
      ↔
    w ∈ BatchLanguage H K := by
  rw [reconstructionMaterializedCYKMember]
  rw [cykStartMember_eq_true_iff]
  have hterm :
      reconstructionMaterializedTerminalRule H K =
        reconstructionFactorSlotUnitFreeTerminalRule H K := by
    funext A a
    apply propext
    exact reconstructionMaterializedTerminalRule_iff H K A a
  have hbin :
      reconstructionMaterializedBinaryRule H K =
        reconstructionFactorSlotUnitFreeBinaryRule H K := by
    funext A B C
    apply propext
    exact reconstructionMaterializedBinaryRule_iff H K A B C
  have hstart :
      reconstructionMaterializedStartRule K =
        reconstructionFactorSlotStartRule K := by
    funext A
    apply propext
    exact reconstructionMaterializedStartRule_iff K A
  rw [hterm, hbin, hstart]
  rw [reconstructionFactorSlotUnitFree_untypedStartLanguage_eq_batchLanguage]

end ReconstructionProductionTables

end TCS1
end LeanCfgProject
