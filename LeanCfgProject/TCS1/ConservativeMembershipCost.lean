import LeanCfgProject.TCS1.BinaryMembershipDecision
import LeanCfgProject.TCS1.ConcreteLearnerComplexity
import LeanCfgProject.TCS1.ReconstructionFiniteStateSupport

/-!
# TCS #1 v79: conservative-update CYK cost bridge

The executable CYK development gives an explicit polynomial comparison
envelope in two parameters:

* the number of non-start symbols of the current separated-start SSBNF
  hypothesis; and
* the length of the next positive datum.

The concrete learner-complexity development independently bounds both the
current reconstructed grammar encoding and the next datum by the encoded
positive-data prefix.

This module composes those two layers.  The only representation-level premise
left explicit is the standard encoding sanity condition that the number of
non-start symbols is at most the explicit grammar encoding envelope.  Under
that premise, the keep/rebuild membership test and a possible rebuild admit a
single explicit polynomial envelope in the data prefix seen so far.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ConservativeMembershipCost

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]

/--
The naive CYK comparison envelope is monotone in both grammar size and input
length.
-/
theorem cykNaiveComparisonEnvelope_mono
    {m m' n n' : Nat}
    (hm : m ≤ m')
    (hn : n ≤ n') :
    cykNaiveComparisonEnvelope m n ≤
      cykNaiveComparisonEnvelope m' n' := by
  unfold cykNaiveComparisonEnvelope
  gcongr

/--
A one-parameter CYK envelope obtained by substituting the degree-five current
grammar-size bound and the data-prefix bound on the next input length.
-/
def conservativeCYKPrefixEnvelope
    (prefixNorm : Nat) : Nat :=
  cykNaiveComparisonEnvelope
    (5 * (prefixNorm + 1) ^ 5)
    prefixNorm

/--
The prefix-only CYK budget is literally an explicit polynomial expression.
No asymptotic cost theorem is imported.
-/
theorem conservativeCYKPrefixEnvelope_polynomial_form
    (p : Nat) :
    conservativeCYKPrefixEnvelope p =
      (5 * (p + 1) ^ 5) * p +
        (5 * (p + 1) ^ 5) ^ 3 * p * (p + 1) ^ 3 *
          (1 + 2 * (5 * (p + 1) ^ 5) * (p + 1) ^ 2) +
        (5 * (p + 1) ^ 5) ^ 2 * (p + 1) ^ 2 +
        (5 * (p + 1) ^ 5) := by
  unfold conservativeCYKPrefixEnvelope
  exact
    cykNaiveComparisonEnvelope_polynomial_form
      (5 * (p + 1) ^ 5) p

/--
Paper-facing membership-cost bridge for the conservative learner.

At stage n+1, suppose the finite non-start-symbol count of the current
separated-start SSBNF presentation is bounded by its explicit reconstruction
encoding envelope.  Then the executable CYK membership test is bounded solely
by a polynomial in the encoded positive-data prefix through stage n+1.
-/
theorem concreteConservative_membershipComparison_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n nonterminalCount : Nat)
    (hcount :
      nonterminalCount ≤
        reconstructionOutputEncodingEnvelope
          (reconstructionSampleNorm
            (concreteConservativeHypothesis H datum n))) :
    cykNaiveComparisonEnvelope
        nonterminalCount
        (datum (n + 1)).length
      ≤
    conservativeCYKPrefixEnvelope
      (positiveDataPrefixNorm datum (n + 1)) := by
  let p := positiveDataPrefixNorm datum (n + 1)
  have hcert :=
    concreteConservative_update_size_certificate
      H datum n
  have hm :
      nonterminalCount ≤
        5 * (p + 1) ^ 5 := by
    exact le_trans hcount hcert.2.1
  have hn :
      (datum (n + 1)).length ≤ p := by
    have hword :
        (datum (n + 1)).length + 1 ≤ p := by
      simpa [p] using hcert.1
    omega
  simpa [conservativeCYKPrefixEnvelope, p] using
    (cykNaiveComparisonEnvelope_mono hm hn)


/--
Occurrence-indexed specialization with no external state-count premise.

The reconstructed non-start symbols are generously named by two-cut sampled
factor slots.  Their finite cardinality is already bounded by the explicit
output encoding envelope, so the representation-count assumption of the
generic bridge is discharged internally.
-/
theorem concreteConservative_occurrenceIndexed_membershipComparison_le_prefix
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
      (positiveDataPrefixNorm datum (n + 1)) := by
  exact
    concreteConservative_membershipComparison_le_prefix
      H datum n
      (Fintype.card
        (ReconstructionFactorSlot
          (concreteConservativeHypothesis H datum n)))
      (reconstructionFactorSlot_card_le_outputEncodingEnvelope
        (concreteConservativeHypothesis H datum n))

/--
A single explicit work envelope for one conservative update:
the membership check plus the worst-case reconstruction output work of a
triggered rebuild.
-/
def conservativeUpdateWorkEnvelope
    (prefixNorm : Nat) : Nat :=
  conservativeCYKPrefixEnvelope prefixNorm +
    5 * (prefixNorm + 1) ^ 5

/--
Under the same representation sanity condition, membership plus a possible
rebuild is polynomially bounded by the data prefix.
-/
theorem concreteConservative_update_work_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n nonterminalCount : Nat)
    (hcount :
      nonterminalCount ≤
        reconstructionOutputEncodingEnvelope
          (reconstructionSampleNorm
            (concreteConservativeHypothesis H datum n))) :
    cykNaiveComparisonEnvelope
        nonterminalCount
        (datum (n + 1)).length
      +
    reconstructionOutputEncodingEnvelope
      (reconstructionSampleNorm
        (concreteAccumulatedSample datum (n + 1)))
      ≤
    conservativeUpdateWorkEnvelope
      (positiveDataPrefixNorm datum (n + 1)) := by
  have hmem :=
    concreteConservative_membershipComparison_le_prefix
      H datum n nonterminalCount hcount
  have hcert :=
    concreteConservative_update_size_certificate
      H datum n
  unfold conservativeUpdateWorkEnvelope
  exact Nat.add_le_add hmem hcert.2.2.1


/--
End-to-end occurrence-indexed work bound for one conservative update.

This removes the last abstract nonterminal-count parameter from the cost
composition: membership testing plus a possible rebuild is bounded by one
explicit polynomial in the positive-data prefix.
-/
theorem concreteConservative_occurrenceIndexed_update_work_le_prefix
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat) :
    cykNaiveComparisonEnvelope
        (Fintype.card
          (ReconstructionFactorSlot
            (concreteConservativeHypothesis H datum n)))
        (datum (n + 1)).length
      +
    reconstructionOutputEncodingEnvelope
      (reconstructionSampleNorm
        (concreteAccumulatedSample datum (n + 1)))
      ≤
    conservativeUpdateWorkEnvelope
      (positiveDataPrefixNorm datum (n + 1)) := by
  exact
    concreteConservative_update_work_le_prefix
      H datum n
      (Fintype.card
        (ReconstructionFactorSlot
          (concreteConservativeHypothesis H datum n)))
      (reconstructionFactorSlot_card_le_outputEncodingEnvelope
        (concreteConservativeHypothesis H datum n))


/--
Semantic-state specialization: use the actual observed paper-facing
reconstruction nonterminals rather than the generous occurrence-slot universe.

This is the representation-count bridge needed by the concrete CFG
presentation of R1--R4.
-/
theorem concreteConservative_activeReconstruction_membershipComparison_le_prefix
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
      (positiveDataPrefixNorm datum (n + 1)) := by
  exact
    concreteConservative_membershipComparison_le_prefix
      H datum n
      (@Fintype.card
        (ActiveReconstructionNonterminal
          (concreteConservativeHypothesis H datum n))
        (activeReconstructionNonterminalFintype
          (concreteConservativeHypothesis H datum n)))
      (activeReconstructionNonterminal_card_le_outputEncodingEnvelope
        (concreteConservativeHypothesis H datum n))

/--
End-to-end work bound using the actual finite reconstruction-state support.
No abstract nonterminal-count parameter remains.
-/
theorem concreteConservative_activeReconstruction_update_work_le_prefix
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
      +
    reconstructionOutputEncodingEnvelope
      (reconstructionSampleNorm
        (concreteAccumulatedSample datum (n + 1)))
      ≤
    conservativeUpdateWorkEnvelope
      (positiveDataPrefixNorm datum (n + 1)) := by
  exact
    concreteConservative_update_work_le_prefix
      H datum n
      (@Fintype.card
        (ActiveReconstructionNonterminal
          (concreteConservativeHypothesis H datum n))
        (activeReconstructionNonterminalFintype
          (concreteConservativeHypothesis H datum n)))
      (activeReconstructionNonterminal_card_le_outputEncodingEnvelope
        (concreteConservativeHypothesis H datum n))

end ConservativeMembershipCost

end TCS1
end LeanCfgProject
