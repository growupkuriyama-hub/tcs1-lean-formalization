import LeanCfgProject.TCS1.LinearNormalizationSoundness
import Mathlib.Tactic

/-!
# TCS #1: semantic completeness of the concrete linear normalization

The soundness direction interprets every fresh chain state as a residual spine
language.  Here we prove the converse inclusion constructively.

For a fixed prepared production p, the finite spine is executed from its
endpoint backwards.  The last step is attached either to

* the old core nonterminal of a rule u B v, or
* the terminal endpoint of a terminal-only rule.

Every preceding step then follows because its continuing child is literally
the parent of the next planned step.  A decreasing induction on the step
index therefore yields a concrete terminal/binary derivation from the source
left-hand side.

Combining this local executor with the prepared least-closure semantics proves
that every prepared derivation is reproduced by the concrete linear-spine
grammar.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearNormalizationCompleteness

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- One concrete binary rule executes exactly one semantic spine step. -/
theorem linearConstructed_step_derives
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length)
    {word : List α}
    (dcont :
      UntypedDerives
        (LinearConstructedTerminalRule G)
        (LinearConstructedBinaryRule G)
        (linearStepContinuation G p i) word) :
    UntypedDerives
      (LinearConstructedTerminalRule G)
      (LinearConstructedBinaryRule G)
      (linearStepParent G p i)
      ((linearPlanStep G p i).apply word) := by
  cases hside : (linearPlanStep G p i).side with
  | left =>
      have dwrapper :
          UntypedDerives
            (LinearConstructedTerminalRule G)
            (LinearConstructedBinaryRule G)
            (linearWrapperState G
              (linearPlanStep G p i).terminal)
            [(linearPlanStep G p i).terminal] :=
        UntypedDerives.terminal
          (LinearConstructedTerminalRule.wrapper
            (linearPlanStep G p i).terminal)
      have dbin :=
        UntypedDerives.binary
          (LinearConstructedBinaryRule.left
            p i hside)
          dwrapper dcont
      simpa [LinearSpineStep.apply, hside] using dbin
  | right =>
      have dwrapper :
          UntypedDerives
            (LinearConstructedTerminalRule G)
            (LinearConstructedBinaryRule G)
            (linearWrapperState G
              (linearPlanStep G p i).terminal)
            [(linearPlanStep G p i).terminal] :=
        UntypedDerives.terminal
          (LinearConstructedTerminalRule.wrapper
            (linearPlanStep G p i).terminal)
      have dbin :=
        UntypedDerives.binary
          (LinearConstructedBinaryRule.right
            p i hside)
          dcont dwrapper
      simpa [LinearSpineStep.apply, hside] using dbin

/--
Concrete derivability condition supplied by a normalized plan endpoint.
Terminal endpoints carry their singleton word; core endpoints carry an
already constructed derivation of the old core nonterminal.
-/
def LinearPlanEndpointConstructedDerivable
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (word : List α) : Prop :=
  match (G.rhs p).toPlan.endpoint with
  | .terminal a =>
      word = [a]
  | .core B =>
      UntypedDerives
        (LinearConstructedTerminalRule G)
        (LinearConstructedBinaryRule G)
        (linearOldState G B) word

/--
At the final spine step, the continuing child derives the endpoint word.
-/
theorem linearConstructed_finalContinuation_derives
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (i : Fin (G.rhs p).toPlan.steps.length)
    (hlast :
      i.1 + 1 =
        (G.rhs p).toPlan.steps.length)
    {endpointWord : List α}
    (hendpoint :
      LinearPlanEndpointConstructedDerivable
        G p endpointWord) :
    UntypedDerives
      (LinearConstructedTerminalRule G)
      (LinearConstructedBinaryRule G)
      (linearStepContinuation G p i)
      endpointWord := by
  cases hend : (G.rhs p).toPlan.endpoint with
  | terminal a =>
      rw [LinearPlanEndpointConstructedDerivable, hend] at hendpoint
      subst endpointWord
      have hcont :
          linearStepContinuation G p i =
            linearAuxState G p i := by
        simp [linearStepContinuation, hend]
      rw [hcont]
      exact
        UntypedDerives.terminal
          (LinearConstructedTerminalRule.auxEndpoint
            p a i hend hlast)
  | core B =>
      rw [LinearPlanEndpointConstructedDerivable, hend] at hendpoint
      rw [linearStepContinuation_eq_core_of_last
        G p i B hend hlast]
      exact hendpoint

/--
Execute every step of one nonempty normalized plan, ending at the supplied
concrete endpoint derivation.
-/
theorem linearConstructed_nonemptyPlan_derives
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    {endpointWord : List α}
    (hnonempty :
      (G.rhs p).toPlan.steps ≠ [])
    (hendpoint :
      LinearPlanEndpointConstructedDerivable
        G p endpointWord) :
    UntypedDerives
      (LinearConstructedTerminalRule G)
      (LinearConstructedBinaryRule G)
      (linearOldState G (G.lhs p))
      (applyLinearSpineSteps
        (G.rhs p).toPlan.steps endpointWord) := by
  let steps := (G.rhs p).toPlan.steps
  have hlenpos : 0 < steps.length := by
    cases hsteps : steps with
    | nil =>
        exact False.elim (hnonempty hsteps)
    | cons step rest =>
        simp [hsteps]
  let n := steps.length - 1
  have hnlt : n < steps.length := by
    dsimp [n]
    omega
  let ilast : Fin steps.length := ⟨n, hnlt⟩
  have hlast :
      ilast.1 + 1 = steps.length := by
    dsimp [ilast, n]
    omega
  have dlastCont :
      UntypedDerives
        (LinearConstructedTerminalRule G)
        (LinearConstructedBinaryRule G)
        (linearStepContinuation G p ilast)
        endpointWord := by
    apply
      linearConstructed_finalContinuation_derives
        G p ilast
    · simpa [steps] using hlast
    · exact hendpoint
  have dlastStep :=
    linearConstructed_step_derives
      G p ilast dlastCont
  have dbase :
      UntypedDerives
        (LinearConstructedTerminalRule G)
        (LinearConstructedBinaryRule G)
        (linearStepParent G p ilast)
        (applyLinearSpineSteps
          (steps.drop n) endpointWord) := by
    have hdrop :
        applyLinearSpineSteps
            (steps.drop n) endpointWord
          =
        (steps.get ilast).apply endpointWord := by
      calc
        applyLinearSpineSteps
            (steps.drop n) endpointWord
            =
          (steps.get ilast).apply
            (applyLinearSpineSteps
              (steps.drop (n + 1)) endpointWord) := by
                simpa [ilast] using
                  (applyLinearSpineSteps_drop_get
                    steps ilast endpointWord)
        _ =
          (steps.get ilast).apply endpointWord := by
            rw [hlast]
            simp [applyLinearSpineSteps]
    have hstep :
        linearPlanStep G p ilast =
          steps.get ilast := by
      rfl
    rw [hdrop, ← hstep]
    exact dlastStep
  have hdesc :
      ∀ k (hk : k ≤ n),
        UntypedDerives
          (LinearConstructedTerminalRule G)
          (LinearConstructedBinaryRule G)
          (linearStepParent G p
            ⟨k, lt_of_le_of_lt hk hnlt⟩)
          (applyLinearSpineSteps
            (steps.drop k) endpointWord) := by
    intro k hk
    refine
      Nat.decreasingInduction
        (n := n)
        (motive := fun k hk =>
          UntypedDerives
            (LinearConstructedTerminalRule G)
            (LinearConstructedBinaryRule G)
            (linearStepParent G p
              ⟨k, lt_of_le_of_lt hk hnlt⟩)
            (applyLinearSpineSteps
              (steps.drop k) endpointWord))
        ?_ ?_ hk
    · intro j hj ih
      have hjlt : j < steps.length := by
        omega
      have hnext :
          j + 1 < steps.length := by
        omega
      let i : Fin steps.length := ⟨j, hjlt⟩
      let inext : Fin steps.length :=
        ⟨j + 1, hnext⟩
      have ih' :
          UntypedDerives
            (LinearConstructedTerminalRule G)
            (LinearConstructedBinaryRule G)
            (linearStepParent G p inext)
            (applyLinearSpineSteps
              (steps.drop (j + 1)) endpointWord) := by
        simpa [inext] using ih
      have hcontState :
          linearStepContinuation G p i =
            linearStepParent G p inext := by
        simpa [i, inext] using
          (linearStepContinuation_eq_nextParent
            G p i hnext)
      have dcont :
          UntypedDerives
            (LinearConstructedTerminalRule G)
            (LinearConstructedBinaryRule G)
            (linearStepContinuation G p i)
            (applyLinearSpineSteps
              (steps.drop (j + 1)) endpointWord) := by
        rw [hcontState]
        exact ih'
      have dstep :=
        linearConstructed_step_derives
          G p i dcont
      have hdrop :=
        applyLinearSpineSteps_drop_get
          steps i endpointWord
      have hiStep :
          linearPlanStep G p i =
            steps.get i := by
        rfl
      rw [hdrop]
      rw [← hiStep]
      simpa [i] using dstep
    · simpa [ilast] using dbase
  have hzero := hdesc 0 (Nat.zero_le n)
  let i0 : Fin steps.length := ⟨0, hlenpos⟩
  have hi0 :
      linearStepParent G p i0 =
        linearOldState G (G.lhs p) :=
    linearStepParent_zero G p i0 rfl
  have hzero' :
      UntypedDerives
        (LinearConstructedTerminalRule G)
        (LinearConstructedBinaryRule G)
        (linearStepParent G p i0)
        (applyLinearSpineSteps steps endpointWord) := by
    simpa [i0] using hzero
  rw [hi0] at hzero'
  exact hzero'

/--
For the concrete old-state interpretation, semantic endpoint realization is
exactly the endpoint condition consumed by the finite spine executor.
-/
theorem linearPlanEndpoint_realizes_constructed_iff
    (G : PreparedLinearIndexedCFG N α P)
    (p : P)
    (word : List α) :
    LinearPlanEndpoint.realizes
        (fun A =>
          {u |
            UntypedDerives
              (LinearConstructedTerminalRule G)
              (LinearConstructedBinaryRule G)
              (linearOldState G A) u})
        (G.rhs p).toPlan.endpoint word
      ↔
    LinearPlanEndpointConstructedDerivable
      G p word := by
  unfold LinearPlanEndpointConstructedDerivable
  cases (G.rhs p).toPlan.endpoint <;> rfl

/--
The old-state language of the concrete factorization is closed under every
prepared plan.
-/
theorem linearConstructed_oldLanguage_planClosed
    (G : PreparedLinearIndexedCFG N α P) :
    PreparedLinearPlanClosed G
      (fun A =>
        {word |
          UntypedDerives
            (LinearConstructedTerminalRule G)
            (LinearConstructedBinaryRule G)
            (linearOldState G A) word}) := by
  intro p word hplan
  rcases hplan with
    ⟨endpointWord, hendpoint, hword⟩
  cases hrhs : G.rhs p with
  | terminals head tail =>
      cases tail with
      | nil =>
          have hsteps :
              (G.rhs p).toPlan.steps = [] := by
            simp [hrhs, PreparedLinearRhs.toPlan,
              terminalLinearPlan]
          have hend :
              (G.rhs p).toPlan.endpoint =
                LinearPlanEndpoint.terminal head := by
            simp [hrhs, PreparedLinearRhs.toPlan,
              terminalLinearPlan]
          rw [hend] at hendpoint
          change endpointWord = [head] at hendpoint
          subst endpointWord
          rw [hsteps] at hword
          simp [applyLinearSpineSteps] at hword
          subst word
          exact
            UntypedDerives.terminal
              (LinearConstructedTerminalRule.sourceEndpoint
                p head hend hsteps)
      | cons next rest =>
          have hnonempty :
              (G.rhs p).toPlan.steps ≠ [] := by
            simp [hrhs, PreparedLinearRhs.toPlan,
              terminalLinearPlan]
          have hderivable :
              LinearPlanEndpointConstructedDerivable
                G p endpointWord :=
            (linearPlanEndpoint_realizes_constructed_iff
              G p endpointWord).1 hendpoint
          have d :=
            linearConstructed_nonemptyPlan_derives
              G p hnonempty hderivable
          change
            UntypedDerives
              (LinearConstructedTerminalRule G)
              (LinearConstructedBinaryRule G)
              (linearOldState G (G.lhs p)) word
          rw [hword]
          exact d
  | around left core right hnonunit =>
      have hnonempty :
          (G.rhs p).toPlan.steps ≠ [] := by
        rw [hrhs]
        simp only [PreparedLinearRhs.toPlan]
        exact
          aroundLinearSteps_nonempty_of_nonunit
            left right hnonunit
      have hend :
          (G.rhs p).toPlan.endpoint =
            LinearPlanEndpoint.core core := by
        simp [hrhs, PreparedLinearRhs.toPlan]
      have hcore :
          UntypedDerives
            (LinearConstructedTerminalRule G)
            (LinearConstructedBinaryRule G)
            (linearOldState G core)
            endpointWord := by
        rw [hend] at hendpoint
        exact hendpoint
      have hderivable :
          LinearPlanEndpointConstructedDerivable
            G p endpointWord :=
        (linearPlanEndpoint_realizes_constructed_iff
          G p endpointWord).1 hendpoint
      have d :=
        linearConstructed_nonemptyPlan_derives
          G p hnonempty hderivable
      change
        UntypedDerives
          (LinearConstructedTerminalRule G)
          (LinearConstructedBinaryRule G)
          (linearOldState G (G.lhs p)) word
      rw [hword]
      exact d

/--
Semantic completeness: every prepared derivation is reproduced by the
concrete terminal/binary factorization.
-/
theorem preparedLinearDerives_to_linearConstructed
    (G : PreparedLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d : PreparedLinearDerives G A word) :
    UntypedDerives
      (LinearConstructedTerminalRule G)
      (LinearConstructedBinaryRule G)
      (linearOldState G A) word := by
  have hplan :
      PreparedLinearPlanClosed G
        (fun B =>
          {u |
            UntypedDerives
              (LinearConstructedTerminalRule G)
              (LinearConstructedBinaryRule G)
              (linearOldState G B) u}) :=
    linearConstructed_oldLanguage_planClosed G
  have hclosed :
      PreparedLinearGrammarClosed G
        (fun B =>
          {u |
            UntypedDerives
              (LinearConstructedTerminalRule G)
              (LinearConstructedBinaryRule G)
              (linearOldState G B) u}) :=
    (preparedLinearGrammarClosed_iff_planClosed
      G _).2 hplan
  exact
    preparedLinearDerives_mem_of_closed
      G _ hclosed d

/--
Exact old-state language preservation for the concrete linear normalization.
-/
theorem linearConstructed_old_language_iff_prepared
    (G : PreparedLinearIndexedCFG N α P)
    (A : N)
    (word : List α) :
    UntypedDerives
        (LinearConstructedTerminalRule G)
        (LinearConstructedBinaryRule G)
        (linearOldState G A) word
      ↔
    PreparedLinearDerives G A word := by
  constructor
  · exact linearConstructed_old_derives_to_prepared G
  · exact preparedLinearDerives_to_linearConstructed G

end LinearNormalizationCompleteness

end TCS1
end LeanCfgProject
