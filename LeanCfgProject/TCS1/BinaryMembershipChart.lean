import LeanCfgProject.TCS1.BinaryMembershipRounds

/-!
# TCS #1 v79: executable finite CYK chart step

This module turns the finite candidate spaces from BinaryMembershipKernel into
an actual bottom-up chart update.

For a fixed input length n, a chart is a finite set of triples (A,i,j).  One
update scans the finite type CYKBinaryCandidate N n.  A candidate
(A,B,C,i,k,j) is enabled when

* i < k < j,
* A -> B C is a binary grammar rule, and
* the old chart contains (B,i,k) and (C,k,j).

The output entry (A,i,j) is inserted into the chart.  The update is cumulative,
so chart membership is monotone.  The implementation scans exactly the finite
candidate type whose cardinality was proved polynomial in the previous module.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryMembershipChart

variable {N : Type u}
variable {α : Type v}

/-- The chart type for an input of length n. -/
abbrev CYKChart
    (N : Type u)
    (n : Nat) :=
  Finset (CYKSpan N n)

/-- Project a binary candidate to the chart entry it can create. -/
def cykCandidateOutput
    {N : Type u}
    {n : Nat}
    (c : CYKBinaryCandidate N n) :
    CYKSpan N n :=
  let A := c.1.1
  let i := c.2.1
  let j := c.2.2.2
  (A, (i, j))

/-- Semantic enabling condition for one binary candidate. -/
def CYKCandidateEnabled
    {N : Type u}
    {n : Nat}
    (binaryRule : N → N → N → Prop)
    (old : CYKChart N n)
    (c : CYKBinaryCandidate N n) : Prop :=
  let A := c.1.1
  let B := c.1.2.1
  let C := c.1.2.2
  let i := c.2.1
  let k := c.2.2.1
  let j := c.2.2.2
  i.1 < k.1 ∧
  k.1 < j.1 ∧
  binaryRule A B C ∧
  (B, (i, k)) ∈ old ∧
  (C, (k, j)) ∈ old

/--
All entries produced by one exhaustive binary-candidate scan.
This definition is executable whenever the finite nonterminal type and binary
rule predicate have decidable equality/membership.
-/
def cykProduced
    [Fintype N]
    [DecidableEq N]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    {n : Nat}
    (old : CYKChart N n) :
    CYKChart N n := by
  letI :
      DecidablePred
        (CYKCandidateEnabled binaryRule old) :=
    fun c => by
      unfold CYKCandidateEnabled
      infer_instance
  exact
    (Finset.univ.filter
        (CYKCandidateEnabled binaryRule old)).image
      cykCandidateOutput

/-- Membership characterization for one produced-entry scan. -/
theorem mem_cykProduced_iff
    [Fintype N]
    [DecidableEq N]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    {n : Nat}
    (old : CYKChart N n)
    (e : CYKSpan N n) :
    e ∈ cykProduced binaryRule old ↔
      ∃ c : CYKBinaryCandidate N n,
        CYKCandidateEnabled binaryRule old c ∧
        cykCandidateOutput c = e := by
  classical
  simp [cykProduced]

/-- One cumulative CYK chart update. -/
def cykChartStep
    [Fintype N]
    [DecidableEq N]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    {n : Nat}
    (old : CYKChart N n) :
    CYKChart N n :=
  old ∪ cykProduced binaryRule old

/-- A chart step never deletes previously established entries. -/
theorem cykChartStep_superset
    [Fintype N]
    [DecidableEq N]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    {n : Nat}
    (old : CYKChart N n) :
    old ⊆ cykChartStep binaryRule old := by
  intro x hx
  simp [cykChartStep, hx]

/-- Iterating the executable chart step from any finite seed chart. -/
def cykChartIterate
    [Fintype N]
    [DecidableEq N]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    {n : Nat}
    (seed : CYKChart N n) :
    Nat → CYKChart N n
  | 0 => seed
  | r + 1 =>
      cykChartStep binaryRule
        (cykChartIterate binaryRule seed r)

/-- Successive executable chart rounds are monotone. -/
theorem cykChartIterate_mono_succ
    [Fintype N]
    [DecidableEq N]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    {n : Nat}
    (seed : CYKChart N n)
    (r : Nat) :
    cykChartIterate binaryRule seed r ⊆
      cykChartIterate binaryRule seed (r + 1) := by
  exact
    cykChartStep_superset
      binaryRule
      (cykChartIterate binaryRule seed r)

/-- Every chart has at most |N|(n+1)^2 entries. -/
theorem cykChart_card_le
    [Fintype N]
    [DecidableEq N]
    {n : Nat}
    (chart : CYKChart N n) :
    chart.card ≤
      Fintype.card N * (n + 1) ^ 2 := by
  rw [← cykSpan_card_eq]
  exact Finset.card_le_univ chart

/--
The finite scan performed by one chart update has exactly the already verified
cubic-in-|N|, cubic-in-(n+1) candidate count.
-/
theorem cykChartStep_scan_card_eq
    [Fintype N]
    (n : Nat) :
    Fintype.card (CYKBinaryCandidate N n) =
      (Fintype.card N) ^ 3 * (n + 1) ^ 3 :=
  cykBinaryCandidate_card_eq n

/--
Running n cumulative rounds scans at most the explicit polynomial budget from
BinaryMembershipKernel.
-/
theorem cykChart_nRounds_scan_count
    [Fintype N]
    (n : Nat) :
    n * Fintype.card (CYKBinaryCandidate N n)
      =
    cykRoundScanEnvelope
      (Fintype.card N) n :=
  cyk_full_scan_count n

end BinaryMembershipChart

end TCS1
end LeanCfgProject
