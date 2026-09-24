import LeanCfgProject.TCS1.BinaryMembershipChartExact
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage

/-!
# TCS #1 v79: executable membership for separated-start SSBNF

The manuscript's conservative update theorem uses the standard fact that CFG
membership is polynomial.  The preceding CYK modules now supply a
self-contained executable decision procedure for the exact grammar shape used
by the learner: terminal/binary non-start rules, a finite set of start
children, and one optional start epsilon rule.

This file packages that procedure at the start-language level and records an
explicit finite scan envelope.  No external CFG-membership theorem is needed
for semantic correctness.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryMembershipDecision

variable {N : Type u}
variable {α : Type v}

/--
The proposition decided by the executable CYK procedure.

The first disjunct handles the separated-start epsilon rule.  The second scans
the finite start-symbol type for a child whose full input span occurs in the
saturated CYK chart.
-/
def CYKStartMembership
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (w : Word α) : Prop :=
  (w = [] ∧ epsilonStart) ∨
    ∃ A : N,
      startRule A ∧
      (A, (cykFullLeft w, cykFullRight w)) ∈
        cykChartIterate binaryRule
          (cykTerminalSeed terminalRule w)
          w.length

/-- The start-membership proposition is decidable from the executable chart data. -/
instance instDecidableCYKStartMembership
    [Fintype N]
    [DecidableEq N]
    [DecidableEq α]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    (startRule : N → Prop)
    [DecidablePred startRule]
    (epsilonStart : Prop)
    [Decidable epsilonStart]
    (w : Word α) :
    Decidable
      (CYKStartMembership
        terminalRule binaryRule
        startRule epsilonStart w) := by
  unfold CYKStartMembership
  infer_instance

/-- Exact semantic correctness of the start-language CYK predicate. -/
theorem cykStartMembership_iff
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (w : Word α) :
    CYKStartMembership
        terminalRule binaryRule
        startRule epsilonStart w
      ↔
    UntypedStartDerives
      terminalRule binaryRule
      startRule epsilonStart w := by
  constructor
  · intro h
    rcases h with hEmpty | hNonempty
    · rcases hEmpty with ⟨rfl, heps⟩
      exact UntypedStartDerives.epsilon heps
    · rcases hNonempty with ⟨A, hstart, hchart⟩
      exact
        UntypedStartDerives.nonempty
          hstart
          (cykFullSpan_sound
            terminalRule binaryRule
            A w hchart)
  · intro d
    cases d with
    | @nonempty A _ hstart hder =>
        exact
          Or.inr
            ⟨A, hstart,
              cykFullSpan_complete
                terminalRule binaryRule
                A w hder⟩
    | epsilon heps =>
        exact Or.inl ⟨rfl, heps⟩

/-- Set-valued correctness statement against the learner's start language. -/
theorem cykStartMembership_iff_mem_language
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (w : Word α) :
    CYKStartMembership
        terminalRule binaryRule
        startRule epsilonStart w
      ↔
    w ∈
      UntypedStartLanguage
        terminalRule binaryRule
        startRule epsilonStart := by
  exact
    cykStartMembership_iff
      terminalRule binaryRule
      startRule epsilonStart w

/--
Boolean executable membership test.

The finite existential over start symbols and all chart memberships are
decidable because the chart is a Finset over a finite nonterminal type.
-/
def cykStartMember
    [Fintype N]
    [DecidableEq N]
    [DecidableEq α]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    (startRule : N → Prop)
    [DecidablePred startRule]
    (epsilonStart : Prop)
    [Decidable epsilonStart]
    (w : Word α) : Bool :=
  decide
    (CYKStartMembership
      terminalRule binaryRule
      startRule epsilonStart w)

/-- The Boolean executable test decides exactly the separated-start language. -/
theorem cykStartMember_eq_true_iff
    [Fintype N]
    [DecidableEq N]
    [DecidableEq α]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    (startRule : N → Prop)
    [DecidablePred startRule]
    (epsilonStart : Prop)
    [Decidable epsilonStart]
    (w : Word α) :
    cykStartMember
        terminalRule binaryRule
        startRule epsilonStart w = true
      ↔
    w ∈
      UntypedStartLanguage
        terminalRule binaryRule
        startRule epsilonStart := by
  rw [cykStartMember]
  simp only [decide_eq_true_eq]
  exact
    cykStartMembership_iff_mem_language
      terminalRule binaryRule
      startRule epsilonStart w

/--
Exact primitive candidate-scan count for one membership test:
one terminal seed scan plus |w| complete binary-candidate scans.

The final scan of start children is deliberately recorded separately below.
-/
def cykMembershipCandidateEnvelope
    (nonterminalCount inputLength : Nat) : Nat :=
  nonterminalCount * inputLength +
    cykRoundScanEnvelope
      nonterminalCount inputLength

theorem cykMembershipCandidateEnvelope_exact
    [Fintype N]
    (n : Nat) :
    Fintype.card (CYKTerminalCandidate N n) +
        n * Fintype.card (CYKBinaryCandidate N n)
      =
    cykMembershipCandidateEnvelope
      (Fintype.card N) n := by
  rw [cykTerminalCandidate_card_eq,
    cyk_full_scan_count]
  rfl

/--
Including a final scan over all possible start children still gives the
following explicit polynomial candidate budget.
-/
def cykStartMembershipScanEnvelope
    (nonterminalCount inputLength : Nat) : Nat :=
  cykMembershipCandidateEnvelope
      nonterminalCount inputLength
    + nonterminalCount

theorem cykStartMembershipScanEnvelope_eq
    (m n : Nat) :
    cykStartMembershipScanEnvelope m n =
      m * n +
        n * (m ^ 3 * (n + 1) ^ 3) +
        m := by
  unfold cykStartMembershipScanEnvelope
  unfold cykMembershipCandidateEnvelope
  unfold cykRoundScanEnvelope
  ring

/--
A conservative implementation using linear Finset membership tests also has
an explicit polynomial comparison budget.  Each binary candidate performs at
most two chart lookups, and every chart has at most m(n+1)^2 entries.
-/
def cykNaiveComparisonEnvelope
    (m n : Nat) : Nat :=
  m * n +
    n * (m ^ 3 * (n + 1) ^ 3) *
      (1 + 2 * (m * (n + 1) ^ 2))
    + m * (m * (n + 1) ^ 2 + 1)

/-- The naive finite-set implementation therefore has a manifest polynomial bound. -/
theorem cykNaiveComparisonEnvelope_polynomial_form
    (m n : Nat) :
    cykNaiveComparisonEnvelope m n =
      m * n +
        m ^ 3 * n * (n + 1) ^ 3 *
          (1 + 2 * m * (n + 1) ^ 2)
        + m ^ 2 * (n + 1) ^ 2 + m := by
  unfold cykNaiveComparisonEnvelope
  ring

end BinaryMembershipDecision

end TCS1
end LeanCfgProject
