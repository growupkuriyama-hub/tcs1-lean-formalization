import LeanCfgProject.TCS1.RegularRecognition
import Mathlib.Tactic

/-!
# TCS #1 v126: finite-state control induced by yield typing

This file formalizes the unnumbered control-set paragraph of the current
manuscript.

A finite linear grammar is presented with one distinct production label per
production. A right-hand side is either a terminal word or u B v. The
production-label word of a successful derivation is tracked explicitly.

For a fixed finite-monoid typing H and accepting set F, we build the finite
control automaton whose active states are (A, mu_L, mu_R). The manuscript
mentions one additional accepting state. Since Mathlib's DFA transition is
total, we also add the standard rejecting sink used to totalize invalid label
sequences; this does not change the accepted control language.

We prove the automaton invariant, regularity of the control set, and the
identity between controlled yields and L(G) intersect H^{-1}(F).
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V126YieldTypingControl

variable {N : Type}
variable {α : Type v}
variable {P : Type w}

inductive LabeledLinearRhs
    (N : Type) (α : Type v) where
  | terminal (word : Word α)
  | around (left : Word α) (core : N) (right : Word α)
deriving DecidableEq

structure LabeledLinearGrammar
    (N : Type) (α : Type v) (P : Type w) where
  lhs : P → N
  rhs : P → LabeledLinearRhs N α
  start : N

inductive LabeledLinearDerives
    (G : LabeledLinearGrammar N α P) :
    N → Word P → Word α → Prop
  | terminal
      (p : P) (A : N) (word : Word α)
      (hlhs : G.lhs p = A)
      (hrhs : G.rhs p = .terminal word) :
      LabeledLinearDerives G A [p] word
  | around
      (p : P) (A B : N)
      (left right : Word α)
      {labels : Word P} {word : Word α}
      (hlhs : G.lhs p = A)
      (hrhs : G.rhs p = .around left B right)
      (child : LabeledLinearDerives G B labels word) :
      LabeledLinearDerives G A (p :: labels)
        (left ++ word ++ right)

def LabeledLinearLanguage
    (G : LabeledLinearGrammar N α P) :
    Set (Word α) :=
  {w | ∃ labels : Word P,
    LabeledLinearDerives G G.start labels w}

inductive YieldControlState
    (N : Type) (M : Type) where
  | active (A : N) (muL muR : M)
  | accept
  | dead
deriving DecidableEq, Fintype

noncomputable def yieldControlStep
    {M : Type}
    [Monoid M] [Fintype M]
    [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M) :
    YieldControlState N M → P → YieldControlState N M := by
  classical
  exact fun q p =>
    match q with
    | .accept => .dead
    | .dead => .dead
    | .active A muL muR =>
        if hlhs : G.lhs p = A then
          match G.rhs p with
          | .terminal word =>
              if muL * H.h word * muR ∈ F then
                .accept
              else
                .dead
          | .around left B right =>
              .active B
                (muL * H.h left)
                (H.h right * muR)
        else
          .dead

noncomputable def yieldControlDFA
    {M : Type}
    [Monoid M] [Fintype M]
    [Fintype N] [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M) :
    DFA P (YieldControlState N M) where
  step := yieldControlStep G H F
  start := .active G.start 1 1
  accept := {.accept}

theorem yieldControl_evalFrom_derives_iff
    {M : Type}
    [Monoid M] [Fintype M]
    [Fintype N] [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M)
    {A : N} {labels : Word P} {word : Word α}
    (d : LabeledLinearDerives G A labels word)
    (muL muR : M) :
    (yieldControlDFA G H F).evalFrom
        (.active A muL muR) labels = .accept
      ↔
    muL * H.h word * muR ∈ F := by
  classical
  induction d generalizing muL muR with
  | terminal p A word hlhs hrhs =>
      simp [yieldControlDFA, yieldControlStep, hlhs, hrhs]
  | @around p A B left right labels word hlhs hrhs child ih =>
      rw [DFA.evalFrom_cons]
      simp only [yieldControlDFA, yieldControlStep, hlhs, hrhs,
        dite_true]
      rw [ih (muL * H.h left) (H.h right * muR)]
      rw [H.map_append (left ++ word) right]
      rw [H.map_append left word]
      simp only [mul_assoc]

/-- The rejecting sink is absorbing for every remaining label word. -/
@[simp] theorem yieldControl_evalFrom_dead
    {M : Type}
    [Monoid M] [Fintype M]
    [Fintype N] [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M)
    (labels : Word P) :
    (yieldControlDFA G H F).evalFrom
        (.dead : YieldControlState N M) labels = .dead := by
  induction labels with
  | nil => rfl
  | cons p rest ih =>
      rw [DFA.evalFrom_cons]
      change
        (yieldControlDFA G H F).evalFrom
          ((yieldControlDFA G H F).step .dead p) rest = .dead
      simp [yieldControlDFA, yieldControlStep, ih]

/-- Once the accepting state is reached, any further production label makes
the word invalid and sends the totalized DFA to the rejecting sink. -/
@[simp] theorem yieldControl_evalFrom_accept_cons
    {M : Type}
    [Monoid M] [Fintype M]
    [Fintype N] [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M)
    (p : P) (rest : Word P) :
    (yieldControlDFA G H F).evalFrom
        (.accept : YieldControlState N M) (p :: rest) = .dead := by
  rw [DFA.evalFrom_cons]
  change
    (yieldControlDFA G H F).evalFrom
      ((yieldControlDFA G H F).step .accept p) rest = .dead
  simp [yieldControlDFA, yieldControlStep]

theorem yieldControl_accept_implies_derivation
    {M : Type}
    [Monoid M] [Fintype M]
    [Fintype N] [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M) :
    ∀ (labels : Word P) (A : N) (muL muR : M),
      (yieldControlDFA G H F).evalFrom
          (.active A muL muR) labels = .accept →
      ∃ word : Word α,
        LabeledLinearDerives G A labels word ∧
        muL * H.h word * muR ∈ F := by
  classical
  intro labels
  induction labels with
  | nil =>
      intro A muL muR h
      simp [yieldControlDFA] at h
  | cons p rest ih =>
      intro A muL muR hacc
      rw [DFA.evalFrom_cons] at hacc
      classical
      by_cases hlhs : G.lhs p = A
      · cases hrhs : G.rhs p with
        | terminal word =>
            by_cases hF : muL * H.h word * muR ∈ F
            · by_cases hrest : rest = []
              · subst rest
                refine ⟨word, ?_, hF⟩
                exact LabeledLinearDerives.terminal
                  p A word hlhs hrhs
              · cases rest with
                | nil => exact False.elim (hrest rfl)
                | cons q qs =>
                    simp [yieldControlDFA, yieldControlStep,
                      hlhs, hrhs, hF,
                      yieldControl_evalFrom_dead,
                      yieldControl_evalFrom_accept_cons] at hacc
            · simp [yieldControlDFA, yieldControlStep,
                hlhs, hrhs, hF,
                yieldControl_evalFrom_dead] at hacc
        | around left B right =>
            have hchild :
                (yieldControlDFA G H F).evalFrom
                    (.active B
                      (muL * H.h left)
                      (H.h right * muR))
                    rest = .accept := by
              simpa [yieldControlDFA, yieldControlStep,
                hlhs, hrhs] using hacc
            obtain ⟨word, dword, htype⟩ :=
              ih B (muL * H.h left)
                (H.h right * muR) hchild
            refine
              ⟨left ++ word ++ right,
                LabeledLinearDerives.around
                  p A B left right hlhs hrhs dword,
                ?_⟩
            rw [H.map_append (left ++ word) right]
            rw [H.map_append left word]
            simpa only [mul_assoc] using htype
      · simp [yieldControlDFA, yieldControlStep, hlhs,
          yieldControl_evalFrom_dead] at hacc

theorem yieldControl_accepts_iff
    {M : Type}
    [Monoid M] [Fintype M]
    [Fintype N] [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M)
    (labels : Word P) :
    labels ∈ (yieldControlDFA G H F).accepts
      ↔
    ∃ word : Word α,
      LabeledLinearDerives G G.start labels word ∧
      H.h word ∈ F := by
  constructor
  · intro h
    change
      (yieldControlDFA G H F).evalFrom
        (.active G.start 1 1) labels = .accept at h
    obtain ⟨word, d, ht⟩ :=
      yieldControl_accept_implies_derivation
        G H F labels G.start 1 1 h
    refine ⟨word, d, ?_⟩
    simpa using ht
  · rintro ⟨word, d, ht⟩
    change
      (yieldControlDFA G H F).evalFrom
        (.active G.start 1 1) labels = .accept
    rw [yieldControl_evalFrom_derives_iff G H F d 1 1]
    simpa using ht

theorem yieldControl_isRegular
    {M : Type}
    [Monoid M] [Fintype M]
    [Fintype N] [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M) :
    Language.IsRegular
      ((yieldControlDFA G H F).accepts : Language P) := by
  exact ⟨YieldControlState N M, inferInstance,
    yieldControlDFA G H F, rfl⟩

def YieldControlledLanguage
    {M : Type}
    [Monoid M] [Fintype M]
    [Fintype N] [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M) :
    Set (Word α) :=
  {word |
    ∃ labels : Word P,
      labels ∈ (yieldControlDFA G H F).accepts ∧
      LabeledLinearDerives G G.start labels word}

theorem yieldControlledLanguage_eq_inter
    {M : Type}
    [Monoid M] [Fintype M]
    [Fintype N] [DecidableEq N]
    (G : LabeledLinearGrammar N α P)
    (H : FixedFiniteMonoidHom α M)
    (F : Set M) :
    YieldControlledLanguage G H F
      =
    LabeledLinearLanguage G ∩ RecognizedPreimage H F := by
  apply Set.ext
  intro word
  constructor
  · rintro ⟨labels, hctrl, d⟩
    have heval :
        (yieldControlDFA G H F).evalFrom
          (.active G.start 1 1) labels = .accept := by
      exact hctrl
    have ht0 :=
      (yieldControl_evalFrom_derives_iff
        G H F d 1 1).1 heval
    have ht : H.h word ∈ F := by
      simpa using ht0
    exact ⟨⟨labels, d⟩, ht⟩
  · rintro ⟨⟨labels, d⟩, ht⟩
    refine ⟨labels, ?_, d⟩
    exact
      (yieldControl_accepts_iff G H F labels).2
        ⟨word, d, ht⟩

end V126YieldTypingControl

end TCS1
end LeanCfgProject
