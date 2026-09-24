import LeanCfgProject.TCS1.ReconstructionUnitFreeBridge
import LeanCfgProject.TCS1.BinaryMembershipDecision
import LeanCfgProject.TCS1.ConservativeMembershipCost

/-!
# TCS #1 v79: reconstruction hypothesis to the CYK interface

The semantic presentation bridge is now complete enough to instantiate the
CYK decision layer with the actual reconstructed hypothesis.

For a finite sample K:

* non-start symbols are the finite observed reconstruction symbols;
* R2/R3 are removed semantically by the verified generic unit-elimination
  layer;
* start children are exactly observed symbols with empty outer contexts; and
* the optional start epsilon rule is present exactly when epsilon belongs to K.

The resulting terminal/binary start language is exactly `BatchLanguage H K`.
This file packages that equality directly through `CYKStartMembership` and
the Boolean CYK interface.

The decision instances used here are classical; the remaining implementation
task is therefore sharply isolated to an effective polynomial unit-closure
precomputation for R2/R3.  The chart algorithm, its correctness, and its
comparison-count envelope are already executable/explicit.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ReconstructionCYKBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]

/--
CYK start-membership predicate specialized to the actual reconstructed
hypothesis.  The finite state structure is the observed reconstruction support.
-/
noncomputable def reconstructionCYKStartMembership
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) : Prop := by
  classical
  letI : Fintype (ActiveReconstructionNonterminal K) :=
    activeReconstructionNonterminalFintype K
  exact
    CYKStartMembership
      (reconstructionUnitFreeTerminalRule H K)
      (reconstructionUnitFreeBinaryRule H K)
      (reconstructionActiveStartRule K)
      (([] : Word α) ∈ K)
      w

/-- Exact semantic correctness against the set-driven reconstructed language. -/
theorem reconstructionCYKStartMembership_iff_batchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) :
    reconstructionCYKStartMembership H K w
      ↔
    w ∈ BatchLanguage H K := by
  classical
  letI : Fintype (ActiveReconstructionNonterminal K) :=
    activeReconstructionNonterminalFintype K
  change
    CYKStartMembership
        (reconstructionUnitFreeTerminalRule H K)
        (reconstructionUnitFreeBinaryRule H K)
        (reconstructionActiveStartRule K)
        (([] : Word α) ∈ K)
        w
      ↔
    w ∈ BatchLanguage H K
  rw [cykStartMembership_iff_mem_language]
  rw [reconstructionUnitFree_untypedStartLanguage_eq_batchLanguage]

/--
Boolean CYK membership test for the reconstructed hypothesis.

This wrapper is marked noncomputable only because the unit-closure predicates
are currently discharged with classical decidability.  The chart itself is
the executable finite algorithm verified in `BinaryMembershipDecision`.
-/
noncomputable def reconstructionCYKMember
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) : Bool := by
  classical
  letI : Fintype (ActiveReconstructionNonterminal K) :=
    activeReconstructionNonterminalFintype K
  exact
    cykStartMember
      (reconstructionUnitFreeTerminalRule H K)
      (reconstructionUnitFreeBinaryRule H K)
      (reconstructionActiveStartRule K)
      (([] : Word α) ∈ K)
      w

/-- The specialized Boolean test accepts exactly `BatchLanguage H K`. -/
theorem reconstructionCYKMember_eq_true_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) :
    reconstructionCYKMember H K w = true
      ↔
    w ∈ BatchLanguage H K := by
  classical
  letI : Fintype (ActiveReconstructionNonterminal K) :=
    activeReconstructionNonterminalFintype K
  change
    cykStartMember
        (reconstructionUnitFreeTerminalRule H K)
        (reconstructionUnitFreeBinaryRule H K)
        (reconstructionActiveStartRule K)
        (([] : Word α) ∈ K)
        w = true
      ↔
    w ∈ BatchLanguage H K
  rw [cykStartMember_eq_true_iff]
  rw [reconstructionUnitFree_untypedStartLanguage_eq_batchLanguage]

/--
Paper-facing combination: the actual finite reconstruction-state count used by
the CYK chart is bounded by the same positive-data-prefix polynomial already
proved for one conservative update.
-/
theorem reconstructionCYK_conservativeComparison_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    cykNaiveComparisonEnvelope
        (@Fintype.card
          (ActiveReconstructionNonterminal
            (concreteConservativeHypothesis H datum n))
          (activeReconstructionNonterminalFintype
            (concreteConservativeHypothesis H datum n)))
        (datum (n + 1)).length
      ≤
    conservativeCYKPrefixEnvelope
      (positiveDataPrefixNorm datum (n + 1)) :=
  concreteConservative_activeReconstruction_membershipComparison_le_prefix
    H datum n

end ReconstructionCYKBridge

end TCS1
end LeanCfgProject
