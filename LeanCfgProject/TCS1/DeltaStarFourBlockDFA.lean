import LeanCfgProject.TCS1.DeltaStarNonlinearityBridge
import LeanCfgProject.TCS1.LinearRegularIntersection

/-!
# TCS #1 v78: DFA for the regular four-block filter

The manuscript's non-linearity reduction intersects Delta-star with

  a* b* a* b*.

This module supplies an explicit five-state DFA for that regular language and
proves exact language equality with FourBlockLanguage. Together with
LinearRegularIntersection, this machine-checks the closure step used in the
manuscript; the only remaining external ingredient is the cited theorem that
Delta Delta itself is not linear.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

inductive FourBlockState where
  | a0
  | b1
  | a2
  | b3
  | sink
  deriving DecidableEq, Fintype, Repr

def fourBlockStep :
    FourBlockState → Symbol → FourBlockState
  | .a0, .a => .a0
  | .a0, .b => .b1
  | .b1, .a => .a2
  | .b1, .b => .b1
  | .a2, .a => .a2
  | .a2, .b => .b3
  | .b3, .a => .sink
  | .b3, .b => .b3
  | .sink, _ => .sink

def fourBlockDFA :
    DFA Symbol FourBlockState where
  step := fourBlockStep
  start := .a0
  accept := {q | q ≠ .sink}

@[simp] theorem fourBlock_evalFrom_sink
    (w : Word Symbol) :
    fourBlockDFA.evalFrom .sink w =
      .sink := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      rw [DFA.evalFrom_cons]
      cases s <;>
        change fourBlockDFA.evalFrom .sink w = .sink <;>
        exact ih

theorem fourBlock_shape_from_b3
    {w : Word Symbol}
    (h :
      fourBlockDFA.evalFrom .b3 w ≠
        .sink) :
    ∃ s : Nat,
      w = List.replicate s b := by
  induction w with
  | nil =>
      exact ⟨0, rfl⟩
  | cons x w ih =>
      cases x with
      | a =>
          exfalso
          apply h
          rw [DFA.evalFrom_cons]
          change
            fourBlockDFA.evalFrom .sink w =
              .sink
          exact fourBlock_evalFrom_sink w
      | b =>
          have htail :
              fourBlockDFA.evalFrom .b3 w ≠
                .sink := by
            simpa [DFA.evalFrom_cons,
              fourBlockDFA, fourBlockStep] using h
          obtain ⟨s, rfl⟩ := ih htail
          exact
            ⟨s + 1,
              by simp [List.replicate_succ,
                replicate_succ_right]⟩

theorem fourBlock_shape_from_a2
    {w : Word Symbol}
    (h :
      fourBlockDFA.evalFrom .a2 w ≠
        .sink) :
    ∃ r s : Nat,
      w =
        List.replicate r a ++
          List.replicate s b := by
  induction w with
  | nil =>
      exact ⟨0, 0, rfl⟩
  | cons x w ih =>
      cases x with
      | a =>
          have htail :
              fourBlockDFA.evalFrom .a2 w ≠
                .sink := by
            simpa [DFA.evalFrom_cons,
              fourBlockDFA, fourBlockStep] using h
          obtain ⟨r, s, hw⟩ := ih htail
          refine ⟨r + 1, s, ?_⟩
          rw [hw]
          simp [List.replicate_succ,
            List.append_assoc]
      | b =>
          have htail :
              fourBlockDFA.evalFrom .b3 w ≠
                .sink := by
            simpa [DFA.evalFrom_cons,
              fourBlockDFA, fourBlockStep] using h
          obtain ⟨s, hw⟩ :=
            fourBlock_shape_from_b3 htail
          refine ⟨0, s + 1, ?_⟩
          rw [hw]
          simp [List.replicate_succ]

theorem fourBlock_shape_from_b1
    {w : Word Symbol}
    (h :
      fourBlockDFA.evalFrom .b1 w ≠
        .sink) :
    ∃ q r s : Nat,
      w =
        List.replicate q b ++
          List.replicate r a ++
            List.replicate s b := by
  induction w with
  | nil =>
      exact ⟨0, 0, 0, rfl⟩
  | cons x w ih =>
      cases x with
      | a =>
          have htail :
              fourBlockDFA.evalFrom .a2 w ≠
                .sink := by
            simpa [DFA.evalFrom_cons,
              fourBlockDFA, fourBlockStep] using h
          obtain ⟨r, s, hw⟩ :=
            fourBlock_shape_from_a2 htail
          refine ⟨0, r + 1, s, ?_⟩
          rw [hw]
          simp [List.replicate_succ,
            List.append_assoc]
      | b =>
          have htail :
              fourBlockDFA.evalFrom .b1 w ≠
                .sink := by
            simpa [DFA.evalFrom_cons,
              fourBlockDFA, fourBlockStep] using h
          obtain ⟨q, r, s, hw⟩ := ih htail
          refine ⟨q + 1, r, s, ?_⟩
          rw [hw]
          simp [List.replicate_succ,
            List.append_assoc]

theorem fourBlock_shape_from_a0
    {w : Word Symbol}
    (h :
      fourBlockDFA.evalFrom .a0 w ≠
        .sink) :
    ∃ p q r s : Nat,
      w =
        List.replicate p a ++
          List.replicate q b ++
            List.replicate r a ++
              List.replicate s b := by
  induction w with
  | nil =>
      exact ⟨0, 0, 0, 0, rfl⟩
  | cons x w ih =>
      cases x with
      | a =>
          have htail :
              fourBlockDFA.evalFrom .a0 w ≠
                .sink := by
            simpa [DFA.evalFrom_cons,
              fourBlockDFA, fourBlockStep] using h
          obtain ⟨p, q, r, s, hw⟩ := ih htail
          refine ⟨p + 1, q, r, s, ?_⟩
          rw [hw]
          simp [List.replicate_succ,
            List.append_assoc]
      | b =>
          have htail :
              fourBlockDFA.evalFrom .b1 w ≠
                .sink := by
            simpa [DFA.evalFrom_cons,
              fourBlockDFA, fourBlockStep] using h
          obtain ⟨q, r, s, hw⟩ :=
            fourBlock_shape_from_b1 htail
          refine ⟨0, q + 1, r, s, ?_⟩
          rw [hw]
          simp [List.replicate_succ,
            List.append_assoc]

@[simp] theorem fourBlock_eval_a0_replicate_a
    (n : Nat) :
    fourBlockDFA.evalFrom .a0
        (List.replicate n a) =
      .a0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [List.replicate_succ,
        DFA.evalFrom_cons]
      change
        fourBlockDFA.evalFrom .a0
            (List.replicate n a) =
          .a0
      exact ih

@[simp] theorem fourBlock_eval_b1_replicate_b
    (n : Nat) :
    fourBlockDFA.evalFrom .b1
        (List.replicate n b) =
      .b1 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [List.replicate_succ,
        DFA.evalFrom_cons]
      change
        fourBlockDFA.evalFrom .b1
            (List.replicate n b) =
          .b1
      exact ih

@[simp] theorem fourBlock_eval_a2_replicate_a
    (n : Nat) :
    fourBlockDFA.evalFrom .a2
        (List.replicate n a) =
      .a2 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [List.replicate_succ,
        DFA.evalFrom_cons]
      change
        fourBlockDFA.evalFrom .a2
            (List.replicate n a) =
          .a2
      exact ih

@[simp] theorem fourBlock_eval_b3_replicate_b
    (n : Nat) :
    fourBlockDFA.evalFrom .b3
        (List.replicate n b) =
      .b3 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [List.replicate_succ,
        DFA.evalFrom_cons]
      change
        fourBlockDFA.evalFrom .b3
            (List.replicate n b) =
          .b3
      exact ih


@[simp] theorem fourBlock_eval_a0_replicate_b_succ
    (n : Nat) :
    fourBlockDFA.evalFrom .a0
        (List.replicate (n + 1) b) =
      .b1 := by
  rw [List.replicate_succ,
    DFA.evalFrom_cons]
  change
    fourBlockDFA.evalFrom .b1
        (List.replicate n b) =
      .b1
  exact fourBlock_eval_b1_replicate_b n

@[simp] theorem fourBlock_eval_b1_replicate_a_succ
    (n : Nat) :
    fourBlockDFA.evalFrom .b1
        (List.replicate (n + 1) a) =
      .a2 := by
  rw [List.replicate_succ,
    DFA.evalFrom_cons]
  change
    fourBlockDFA.evalFrom .a2
        (List.replicate n a) =
      .a2
  exact fourBlock_eval_a2_replicate_a n

@[simp] theorem fourBlock_eval_a2_replicate_b_succ
    (n : Nat) :
    fourBlockDFA.evalFrom .a2
        (List.replicate (n + 1) b) =
      .b3 := by
  rw [List.replicate_succ,
    DFA.evalFrom_cons]
  change
    fourBlockDFA.evalFrom .b3
        (List.replicate n b) =
      .b3
  exact fourBlock_eval_b3_replicate_b n

theorem fourBlock_shape_accepted
    (p q r s : Nat) :
    fourBlockDFA.eval
        (List.replicate p a ++
          List.replicate q b ++
            List.replicate r a ++
              List.replicate s b) ≠
      .sink := by
  change
    fourBlockDFA.evalFrom .a0
        (List.replicate p a ++
          List.replicate q b ++
            List.replicate r a ++
              List.replicate s b) ≠
      .sink
  simp only [DFA.evalFrom_of_append,
    fourBlock_eval_a0_replicate_a]
  cases q with
  | zero =>
      simp only [List.replicate_zero,
        DFA.evalFrom_nil]
      rw [fourBlock_eval_a0_replicate_a]
      cases s with
      | zero =>
          simp
      | succ s =>
          have h :=
            fourBlock_eval_a0_replicate_b_succ s
          simpa using h
  | succ q =>
      rw [fourBlock_eval_a0_replicate_b_succ]
      cases r with
      | zero =>
          simp only [List.replicate_zero,
            DFA.evalFrom_nil]
          rw [fourBlock_eval_b1_replicate_b]
          simp
      | succ r =>
          rw [fourBlock_eval_b1_replicate_a_succ]
          cases s with
          | zero =>
              simp
          | succ s =>
              rw [fourBlock_eval_a2_replicate_b_succ]
              simp

theorem fourBlockDFA_accepts_eq :
    fourBlockDFA.accepts =
      FourBlockLanguage := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    change
      fourBlockDFA.evalFrom .a0 w ≠
        .sink at hw
    exact fourBlock_shape_from_a0 hw
  · rintro ⟨p, q, r, s, rfl⟩
    exact
      fourBlock_shape_accepted p q r s

end DeltaStar
end TCS1
end LeanCfgProject
