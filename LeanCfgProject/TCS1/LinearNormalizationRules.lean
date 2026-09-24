import LeanCfgProject.TCS1.LinearNormalizationPlan
import LeanCfgProject.TCS1.LinearTypedShapeBridge
import Mathlib.Data.Fintype.BigOperators

/-!
# TCS #1: concrete terminal/binary rule construction for linear normalization

This module assigns finite fresh names to the exact spine plans from
LinearNormalizationPlan.

For each prepared production p, one auxiliary state is allocated for every
binary spine step. In the u B v case the final allocated auxiliary slot is
unused (the final spine step continues directly to B); this harmless generous
allocation makes the finite construction uniform and is still linear in the
source right-hand-side size.

The resulting non-start grammar has:

* one shared wrapper state W_a with W_a -> a for every terminal a;
* terminal endpoint rules for terminal-only source productions; and
* one binary rule for every planned spine step.

We prove directly that every binary production has exactly one wrapper child
and one non-wrapper continuing child. Thus the concrete output satisfies the
syntactic linear-spine condition required by Section 8.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearNormalizationRules

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- One generous fresh auxiliary slot for every planned binary spine step. -/
abbrev LinearPlanAuxIndex
    (G : PreparedLinearIndexedCFG N α P) :=
  Sigma (fun p : P =>
    Fin (G.rhs p).toPlan.steps.length)

/--
Concrete non-start state universe of the linear normalization:
old symbols, shared terminal wrappers, and per-production chain states.
-/
abbrev LinearConstructedState
    (G : PreparedLinearIndexedCFG N α P) :=
  N ⊕ (α ⊕ LinearPlanAuxIndex G)

def linearOldState
    (G : PreparedLinearIndexedCFG N α P)
    (A : N) :
    LinearConstructedState G :=
  Sum.inl A

def linearWrapperState
    (G : PreparedLinearIndexedCFG N α P)
    (a : α) :
    LinearConstructedState G :=
  Sum.inr (Sum.inl a)

def linearAuxState
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length) :
    LinearConstructedState G :=
  Sum.inr (Sum.inr ⟨p, i⟩)

/-- The concrete spine step stored at one auxiliary position. -/
def linearPlanStep
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length) :
    LinearSpineStep α :=
  (G.rhs p).toPlan.steps.get i

/--
Parent state of one planned binary step. The first step is headed by the
source left-hand side; every later step is headed by the preceding auxiliary
state.
-/
def linearStepParent
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length) :
    LinearConstructedState G :=
  if _hzero : i.1 = 0 then
    linearOldState G (G.lhs p)
  else
    linearAuxState G p
      ⟨i.1 - 1,
        lt_of_le_of_lt
          (Nat.sub_le i.1 1) i.2⟩

/--
Continuing child of one planned binary step.

For terminal-only plans every step continues to its allocated auxiliary state,
and the last such state carries the final terminal rule. For u B v plans,
every nonfinal step continues to its auxiliary state while the final step
continues directly to B.
-/
def linearStepContinuation
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length) :
    LinearConstructedState G :=
  match (G.rhs p).toPlan.endpoint with
  | .terminal _ =>
      linearAuxState G p i
  | .core B =>
      if _hnext :
          i.1 + 1 < (G.rhs p).toPlan.steps.length then
        linearAuxState G p i
      else
        linearOldState G B


@[simp] theorem linearStepParent_zero
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length)
    (hzero : i.1 = 0) :
    linearStepParent G p i =
      linearOldState G (G.lhs p) := by
  simp [linearStepParent, hzero]

/--
At every nonfinal position, the current continuing child is literally the
parent state of the next planned step.
-/
theorem linearStepContinuation_eq_nextParent
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length)
    (hnext :
      i.1 + 1 < (G.rhs p).toPlan.steps.length) :
    linearStepContinuation G p i =
      linearStepParent G p
        ⟨i.1 + 1, hnext⟩ := by
  have hne : i.1 + 1 ≠ 0 := by
    omega
  cases hend : (G.rhs p).toPlan.endpoint with
  | terminal a =>
      simp [linearStepContinuation, linearStepParent,
        hend, hnext, hne]
  | core B =>
      simp [linearStepContinuation, linearStepParent,
        hend, hnext, hne]

/-- At a final core-ending step, the continuation is the old core symbol. -/
theorem linearStepContinuation_eq_core_of_last
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length)
    (B : N)
    (hend :
      (G.rhs p).toPlan.endpoint =
        LinearPlanEndpoint.core B)
    (hlast :
      i.1 + 1 =
        (G.rhs p).toPlan.steps.length) :
    linearStepContinuation G p i =
      linearOldState G B := by
  unfold linearStepContinuation
  rw [hend]
  simp [hlast]

/-- Terminal rules of the concretely factorized non-start grammar. -/
inductive LinearConstructedTerminalRule
    (G : PreparedLinearIndexedCFG N α P) :
    LinearConstructedState G → α → Prop
  | wrapper
      (a : α) :
      LinearConstructedTerminalRule G
        (linearWrapperState G a) a
  | sourceEndpoint
      (p : P) (a : α)
      (hend :
        (G.rhs p).toPlan.endpoint =
          LinearPlanEndpoint.terminal a)
      (hsteps :
        (G.rhs p).toPlan.steps = []) :
      LinearConstructedTerminalRule G
        (linearOldState G (G.lhs p)) a
  | auxEndpoint
      (p : P) (a : α)
      (i : Fin (G.rhs p).toPlan.steps.length)
      (hend :
        (G.rhs p).toPlan.endpoint =
          LinearPlanEndpoint.terminal a)
      (hlast :
        i.1 + 1 =
          (G.rhs p).toPlan.steps.length) :
      LinearConstructedTerminalRule G
        (linearAuxState G p i) a

/-- Binary rules: exactly one rule for each planned terminal-emitting step. -/
inductive LinearConstructedBinaryRule
    (G : PreparedLinearIndexedCFG N α P) :
    LinearConstructedState G →
    LinearConstructedState G →
    LinearConstructedState G → Prop
  | left
      (p : P)
      (i : Fin (G.rhs p).toPlan.steps.length)
      (hside :
        (linearPlanStep G p i).side =
          LinearSpineSide.left) :
      LinearConstructedBinaryRule G
        (linearStepParent G p i)
        (linearWrapperState G
          (linearPlanStep G p i).terminal)
        (linearStepContinuation G p i)
  | right
      (p : P)
      (i : Fin (G.rhs p).toPlan.steps.length)
      (hside :
        (linearPlanStep G p i).side =
          LinearSpineSide.right) :
      LinearConstructedBinaryRule G
        (linearStepParent G p i)
        (linearStepContinuation G p i)
        (linearWrapperState G
          (linearPlanStep G p i).terminal)

/-- Concrete wrapper predicate on the constructed state universe. -/
def LinearConstructedWrapper
    (G : PreparedLinearIndexedCFG N α P) :
    LinearConstructedState G → Prop
  | Sum.inr (Sum.inl _) => True
  | _ => False

@[simp] theorem linearConstructedWrapper_wrapper
    (G : PreparedLinearIndexedCFG N α P)
    (a : α) :
    LinearConstructedWrapper G
      (linearWrapperState G a) := by
  trivial

@[simp] theorem linearConstructedWrapper_old
    (G : PreparedLinearIndexedCFG N α P)
    (A : N) :
    ¬ LinearConstructedWrapper G
      (linearOldState G A) := by
  simp [LinearConstructedWrapper, linearOldState]

@[simp] theorem linearConstructedWrapper_aux
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length) :
    ¬ LinearConstructedWrapper G
      (linearAuxState G p i) := by
  simp [LinearConstructedWrapper, linearAuxState]

/-- A planned step parent is never a wrapper. -/
theorem linearStepParent_not_wrapper
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length) :
    ¬ LinearConstructedWrapper G
      (linearStepParent G p i) := by
  unfold linearStepParent
  split
  · simp
  · simp

/-- A planned continuing child is never a wrapper. -/
theorem linearStepContinuation_not_wrapper
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length) :
    ¬ LinearConstructedWrapper G
      (linearStepContinuation G p i) := by
  unfold linearStepContinuation
  split
  · simp
  · split
    · simp
    · simp

/--
The concrete factorized grammar satisfies the untyped linear-spine shape
directly.
-/
theorem linearConstructed_untypedLinearSpineShape
    (G : PreparedLinearIndexedCFG N α P) :
    UntypedLinearSpineShape
      (LinearConstructedTerminalRule G)
      (LinearConstructedBinaryRule G)
      (LinearConstructedWrapper G) := by
  refine
    { wrapper_terminal := ?_
      wrapper_no_binary := ?_
      binary_children := ?_ }
  · intro X hwrap
    rcases X with A | rest
    · simp [LinearConstructedWrapper] at hwrap
    · rcases rest with a | aux
      · exact
          ⟨a,
            LinearConstructedTerminalRule.wrapper a⟩
      · simp [LinearConstructedWrapper] at hwrap
  · intro A B C hwrap hbin
    cases hbin with
    | left p i hside =>
        exact
          (linearStepParent_not_wrapper G p i)
            hwrap
    | right p i hside =>
        exact
          (linearStepParent_not_wrapper G p i)
            hwrap
  · intro A B C hbin
    cases hbin with
    | left p i hside =>
        left
        exact
          ⟨linearConstructedWrapper_wrapper G _,
            linearStepContinuation_not_wrapper G p i⟩
    | right p i hside =>
        right
        exact
          ⟨linearStepContinuation_not_wrapper G p i,
            linearConstructedWrapper_wrapper G _⟩

/-- Total number of planned binary steps in an indexed prepared grammar. -/
def PreparedLinearIndexedCFG.totalPlanSteps
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) : Nat :=
  ∑ p : P, (G.rhs p).toPlan.steps.length

/-- Planned binary-step count is the sum of the per-rule binary counts. -/
theorem preparedLinear_totalPlanSteps_eq
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    G.totalPlanSteps =
      ∑ p : P, (G.rhs p).binaryCount := by
  classical
  unfold PreparedLinearIndexedCFG.totalPlanSteps
  apply Finset.sum_congr rfl
  intro p hp
  exact PreparedLinearRhs.toPlan_steps_length (G.rhs p)

/-- Per-rule binary-step count is bounded by source RHS length. -/
theorem PreparedLinearRhs.binaryCount_le_sourceLength
    (rhs : PreparedLinearRhs N α) :
    rhs.binaryCount ≤ rhs.sourceLength := by
  cases rhs with
  | terminals head tail =>
      simp [PreparedLinearRhs.binaryCount,
        PreparedLinearRhs.sourceLength]
  | around left core right hnonunit =>
      simp [PreparedLinearRhs.binaryCount,
        PreparedLinearRhs.sourceLength]

/-- Total planned binary-step count is linear in source RHS size. -/
theorem preparedLinear_totalPlanSteps_le_totalSourceLength
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    G.totalPlanSteps ≤ G.totalSourceLength := by
  classical
  unfold PreparedLinearIndexedCFG.totalPlanSteps
  unfold PreparedLinearIndexedCFG.totalSourceLength
  apply Finset.sum_le_sum
  intro p hp
  rw [PreparedLinearRhs.toPlan_steps_length]
  exact
    PreparedLinearRhs.binaryCount_le_sourceLength
      (G.rhs p)

/-- The concrete auxiliary index has exactly one slot per planned step. -/
@[simp] theorem linearPlanAuxIndex_card
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearPlanAuxIndex G) =
      G.totalPlanSteps := by
  classical
  simp [LinearPlanAuxIndex,
    PreparedLinearIndexedCFG.totalPlanSteps]

/-- Exact cardinality of the concrete constructed state universe. -/
@[simp] theorem linearConstructedState_card
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearConstructedState G) =
      Fintype.card N + Fintype.card α +
        G.totalPlanSteps := by
  rw [Fintype.card_sum, Fintype.card_sum]
  rw [linearPlanAuxIndex_card G]
  omega

/-- The concrete rule construction has a linear-size state universe. -/
theorem linearConstructedState_card_le_scale
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearConstructedState G) ≤
      G.encodingScale := by
  rw [linearConstructedState_card]
  have hsteps :=
    preparedLinear_totalPlanSteps_le_totalSourceLength G
  unfold PreparedLinearIndexedCFG.encodingScale
  omega


/-- Source productions whose normalized plan has a terminal endpoint. -/
abbrev LinearEndpointTerminalIndex
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :=
  {p : P //
    ∃ a : α,
      (G.rhs p).toPlan.endpoint =
        LinearPlanEndpoint.terminal a}


noncomputable instance linearEndpointTerminalIndexFintype
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype (LinearEndpointTerminalIndex G) :=
  Fintype.ofFinite _

/-- One index per concrete terminal rule family member. -/
abbrev LinearConstructedTerminalRuleIndex
    [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :=
  α ⊕ LinearEndpointTerminalIndex G

/-- One index per concrete binary rule. -/
abbrev LinearConstructedBinaryRuleIndex
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :=
  LinearPlanAuxIndex G

/-- Endpoint terminal-rule indices are a subtype of the source productions. -/
theorem linearEndpointTerminalIndex_card_le
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearEndpointTerminalIndex G) ≤
      Fintype.card P := by
  exact Fintype.card_subtype_le _

/-- Concrete terminal-rule index count is at most wrappers plus source rules. -/
theorem linearConstructedTerminalRuleIndex_card_le
    [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearConstructedTerminalRuleIndex G) ≤
      Fintype.card α + Fintype.card P := by
  rw [Fintype.card_sum]
  exact Nat.add_le_add_left
    (linearEndpointTerminalIndex_card_le G)
    (Fintype.card α)

/-- Concrete binary-rule index count is exactly the planned-step count. -/
@[simp] theorem linearConstructedBinaryRuleIndex_card
    [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearConstructedBinaryRuleIndex G) =
      G.totalPlanSteps := by
  exact linearPlanAuxIndex_card G

/-- The concrete normalized rule-index count is bounded by the source scale. -/
theorem linearConstructedRuleIndex_card_le_scale
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearConstructedTerminalRuleIndex G) +
        Fintype.card (LinearConstructedBinaryRuleIndex G)
      ≤
    G.encodingScale := by
  have ht :=
    linearConstructedTerminalRuleIndex_card_le G
  have hb :=
    preparedLinear_totalPlanSteps_le_totalSourceLength G
  rw [linearConstructedBinaryRuleIndex_card]
  unfold PreparedLinearIndexedCFG.encodingScale
  omega

/--
The actual constructed state and rule index spaces together are at most twice
the prepared encoding scale.
-/
theorem linearConstructed_combined_size_le_twice_scale
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    Fintype.card (LinearConstructedState G) +
      (Fintype.card (LinearConstructedTerminalRuleIndex G) +
       Fintype.card (LinearConstructedBinaryRuleIndex G))
      ≤
    2 * G.encodingScale := by
  have hs :=
    linearConstructedState_card_le_scale G
  have hr :=
    linearConstructedRuleIndex_card_le_scale G
  omega


/--
Structural and size conclusions of the appendix construction, packaged
together for the concrete prepared grammar.
-/
theorem linearConstructed_shape_and_size
    [Fintype N] [Fintype α] [Fintype P]
    (G : PreparedLinearIndexedCFG N α P) :
    UntypedLinearSpineShape
      (LinearConstructedTerminalRule G)
      (LinearConstructedBinaryRule G)
      (LinearConstructedWrapper G)
    ∧
    Fintype.card (LinearConstructedState G) +
      (Fintype.card (LinearConstructedTerminalRuleIndex G) +
       Fintype.card (LinearConstructedBinaryRuleIndex G))
      ≤
    2 * G.encodingScale := by
  exact
    ⟨linearConstructed_untypedLinearSpineShape G,
      linearConstructed_combined_size_le_twice_scale G⟩

end LinearNormalizationRules

end TCS1
end LeanCfgProject
