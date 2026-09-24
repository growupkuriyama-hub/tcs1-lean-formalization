import LeanCfgProject.TCS1.BinaryUnitElimination
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# TCS #1 v79: executable finite unit reachability

Unit elimination in the reconstruction grammar needs the reflexive-transitive
closure of a finite unary-rule relation.  This file makes that closure
executable instead of leaving it as a classical `UnitReach` proposition.

For a finite state type N, start from {A} and repeatedly add every one-step
unit successor.  The sequence is monotone.  If one stage is unchanged then all
later stages are unchanged; otherwise cardinality strictly increases.  Hence
after at most |N| rounds the process is stable.  The stable set is closed under
unit edges and therefore contains exactly the states reachable by
`UnitReach`.

This supplies both:

* an exact finite decision procedure for unit reachability; and
* the cubic primitive scan count |N| rounds x |N|^2 edge candidates.

It is the remaining finite-graph component needed to make the reconstructed
hypothesis membership test computational rather than merely classically
decidable.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section FiniteUnitReachability

variable {N : Type u}
variable [Fintype N] [DecidableEq N]

/-- One breadth-style closure step for a decidable unit relation. -/
def finiteUnitReachStep
    (unit : N → N → Prop)
    [DecidableRel unit]
    (S : Finset N) :
    Finset N :=
  S ∪
    Finset.univ.filter
      (fun y => ∃ x ∈ S, unit x y)

@[simp] theorem mem_finiteUnitReachStep_iff
    (unit : N → N → Prop)
    [DecidableRel unit]
    (S : Finset N)
    (y : N) :
    y ∈ finiteUnitReachStep unit S
      ↔
    y ∈ S ∨ ∃ x ∈ S, unit x y := by
  simp [finiteUnitReachStep]

/-- Reachable-state approximation after a bounded number of closure rounds. -/
def finiteUnitReachSet
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A : N) :
    Nat → Finset N
  | 0 => {A}
  | n + 1 =>
      finiteUnitReachStep unit
        (finiteUnitReachSet unit A n)

/-- Every round preserves all states found by the previous round. -/
theorem finiteUnitReachSet_subset_succ
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A : N)
    (n : Nat) :
    finiteUnitReachSet unit A n ⊆
      finiteUnitReachSet unit A (n + 1) := by
  intro x hx
  simp [finiteUnitReachSet,
    finiteUnitReachStep, hx]

/-- The source state remains present at every round. -/
theorem finiteUnitReachSet_source_mem
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A : N) :
    ∀ n,
      A ∈ finiteUnitReachSet unit A n := by
  intro n
  induction n with
  | zero =>
      simp [finiteUnitReachSet]
  | succ n ih =>
      exact
        finiteUnitReachSet_subset_succ
          unit A n ih

/-- Every state found by the finite closure has a genuine UnitReach path. -/
theorem finiteUnitReachSet_sound
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A : N)
    {B : N} :
    ∀ {n},
      B ∈ finiteUnitReachSet unit A n →
        UnitReach unit A B := by
  intro n hB
  induction n generalizing B with
  | zero =>
      simp [finiteUnitReachSet] at hB
      subst B
      exact UnitReach.refl A
  | succ n ih =>
      have hstep :
          B ∈ finiteUnitReachSet unit A n ∨
            ∃ X ∈ finiteUnitReachSet unit A n,
              unit X B := by
        simpa [finiteUnitReachSet] using hB
      rcases hstep with hold | hnew
      · exact ih hold
      · rcases hnew with ⟨X, hX, hXB⟩
        exact
          UnitReach.trans
            (ih hX)
            (UnitReach.single hXB)

/-- If one stage is fixed, the following stage is fixed as well. -/
theorem finiteUnitReachSet_next_eq_of_eq
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A : N)
    {n : Nat}
    (h :
      finiteUnitReachSet unit A n =
        finiteUnitReachSet unit A (n + 1)) :
    finiteUnitReachSet unit A (n + 1) =
      finiteUnitReachSet unit A (n + 2) := by
  have h' :=
    congrArg (finiteUnitReachStep unit) h
  simpa [finiteUnitReachSet,
    Nat.add_assoc] using h'

/-- A non-fixed round strictly increases finite-set cardinality. -/
theorem finiteUnitReachSet_card_lt_succ_of_ne
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A : N)
    (n : Nat)
    (hne :
      finiteUnitReachSet unit A n ≠
        finiteUnitReachSet unit A (n + 1)) :
    (finiteUnitReachSet unit A n).card <
      (finiteUnitReachSet unit A (n + 1)).card := by
  have hsub :=
    finiteUnitReachSet_subset_succ
      unit A n
  have hss :
      finiteUnitReachSet unit A n ⊂
        finiteUnitReachSet unit A (n + 1) :=
    (Finset.ssubset_iff_subset_ne).2
      ⟨hsub, hne⟩
  exact Finset.card_lt_card hss

/--
If round n has not stabilized, at least n+1 distinct states have already been
found.
-/
theorem finiteUnitReachSet_card_ge_of_not_fixed
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A : N) :
    ∀ n,
      finiteUnitReachSet unit A n ≠
          finiteUnitReachSet unit A (n + 1) →
        n + 1 ≤
          (finiteUnitReachSet unit A n).card := by
  intro n
  induction n with
  | zero =>
      intro _hne
      simp [finiteUnitReachSet]
  | succ n ih =>
      intro hne
      have hprev :
          finiteUnitReachSet unit A n ≠
            finiteUnitReachSet unit A (n + 1) := by
        intro heq
        have hnext :=
          finiteUnitReachSet_next_eq_of_eq
            unit A heq
        exact hne hnext
      have hge := ih hprev
      have hlt :=
        finiteUnitReachSet_card_lt_succ_of_ne
          unit A n hprev
      omega

/-- The closure has stabilized after at most |N| rounds. -/
theorem finiteUnitReachSet_stable_at_card
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A : N) :
    finiteUnitReachSet unit A (Fintype.card N) =
      finiteUnitReachSet unit A (Fintype.card N + 1) := by
  by_contra hne
  have hge :=
    finiteUnitReachSet_card_ge_of_not_fixed
      unit A (Fintype.card N) hne
  have hle :
      (finiteUnitReachSet
        unit A (Fintype.card N)).card ≤
      Fintype.card N :=
    Finset.card_le_univ _
  omega

/-- Membership is preserved by every edge once a closure set is fixed. -/
theorem finiteUnitReachStep_closed_of_fixed
    (unit : N → N → Prop)
    [DecidableRel unit]
    (S : Finset N)
    (hfix : S = finiteUnitReachStep unit S)
    {X Y : N}
    (hX : X ∈ S)
    (hXY : unit X Y) :
    Y ∈ S := by
  have hYstep :
      Y ∈ finiteUnitReachStep unit S := by
    exact
      (mem_finiteUnitReachStep_iff
        unit S Y).2
        (Or.inr ⟨X, hX, hXY⟩)
  rw [← hfix] at hYstep
  exact hYstep

/-- Any edge-closed set containing the source contains every UnitReach target. -/
theorem unitReach_mem_of_edge_closed
    (unit : N → N → Prop)
    (S : Finset N)
    (hclosed :
      ∀ {X Y : N},
        X ∈ S → unit X Y → Y ∈ S) :
    ∀ {A B : N},
      UnitReach unit A B →
      A ∈ S →
      B ∈ S := by
  intro A B hreach
  induction hreach with
  | refl A =>
      intro hA
      exact hA
  | @step A B C hAB hBC ih =>
      intro hA
      exact ih (hclosed hA hAB)

/-- Every genuine UnitReach target is present after |N| closure rounds. -/
theorem finiteUnitReachSet_complete
    (unit : N → N → Prop)
    [DecidableRel unit]
    {A B : N}
    (hreach : UnitReach unit A B) :
    B ∈
      finiteUnitReachSet
        unit A (Fintype.card N) := by
  let S :=
    finiteUnitReachSet
      unit A (Fintype.card N)
  have hstable :=
    finiteUnitReachSet_stable_at_card
      unit A
  have hfix :
      S = finiteUnitReachStep unit S := by
    simpa [S, finiteUnitReachSet] using hstable
  have hclosed :
      ∀ {X Y : N},
        X ∈ S → unit X Y → Y ∈ S := by
    intro X Y hX hXY
    exact
      finiteUnitReachStep_closed_of_fixed
        unit S hfix hX hXY
  have hA : A ∈ S := by
    simpa [S] using
      finiteUnitReachSet_source_mem
        unit A (Fintype.card N)
  exact
    unitReach_mem_of_edge_closed
      unit S hclosed hreach hA

/-- Exact finite characterization of reflexive-transitive unit reachability. -/
theorem mem_finiteUnitReachSet_card_iff
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A B : N) :
    B ∈
        finiteUnitReachSet
          unit A (Fintype.card N)
      ↔
    UnitReach unit A B := by
  constructor
  · exact
      finiteUnitReachSet_sound unit A
  · exact
      finiteUnitReachSet_complete unit

/-- Executable Boolean unit-reachability test. -/
def finiteUnitReach
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A B : N) : Bool :=
  decide
    (B ∈
      finiteUnitReachSet
        unit A (Fintype.card N))

/-- The Boolean test is exact. -/
theorem finiteUnitReach_eq_true_iff
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A B : N) :
    finiteUnitReach unit A B = true
      ↔
    UnitReach unit A B := by
  rw [finiteUnitReach]
  simp only [decide_eq_true_eq]
  exact mem_finiteUnitReachSet_card_iff unit A B

/-- Computable Decidable instance for UnitReach on a finite decidable graph. -/
instance instDecidableUnitReachFinite
    (unit : N → N → Prop)
    [DecidableRel unit]
    (A B : N) :
    Decidable (UnitReach unit A B) :=
  decidable_of_iff
    (B ∈ finiteUnitReachSet
      unit A (Fintype.card N))
    (mem_finiteUnitReachSet_card_iff
      unit A B)

/-- Primitive edge-candidate scan count for the |N|-round closure. -/
def finiteUnitReachScanEnvelope
    (stateCount : Nat) : Nat :=
  stateCount * stateCount ^ 2

theorem finiteUnitReachScanEnvelope_eq
    (m : Nat) :
    finiteUnitReachScanEnvelope m = m ^ 3 := by
  unfold finiteUnitReachScanEnvelope
  ring

end FiniteUnitReachability

end TCS1
end LeanCfgProject
