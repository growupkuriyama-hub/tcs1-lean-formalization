import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Relation

/-!
# TCS #1 v158: deterministic pushdown automata (general definition)

Neither Mathlib nor this repository contained a pushdown-automaton model, so this
file gives the standard textbook definition, used to state the
"deterministic context-free" clauses of the manuscript.

A DPDA `M` over input alphabet `σ` has
* a finite set of control states `Q` and a finite stack alphabet `Γ`
  (`Fintype` instances are part of `IsDCFL`);
* a start state, an initial (bottom) stack symbol, and a set of final states;
* a partial transition function
  `trans : Q → Option σ → Γ → Option (Q × List Γ)`:
  `trans q (some a) Z = some (q', γ)` reads `a` with top `Z`, replaces `Z` by `γ`
  (head of `γ` = new top); `trans q none Z` is an ε-move.

**Determinism** is the usual condition: there is at most one move for each
`(q, input symbol or ε, top)` (automatic, `trans` is a function into `Option`),
and if an ε-move is defined for `(q, Z)` then no reading move is defined for
`(q, Z)` (field `det`).  Acceptance is by final state after the whole input
has been read (ε-moves may follow the last symbol).

`DPDA.step_deterministic` proves that the one-step relation on configurations
is functional.  `IsDCFL L` says that some DPDA with finitely many states and
stack symbols accepts exactly `L`; it is **not** a decidability predicate.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

/-- A deterministic pushdown automaton. -/
structure DPDA (Q : Type u) (Γ : Type v) (σ : Type w) where
  start : Q
  bottom : Γ
  final : Q → Prop
  trans : Q → Option σ → Γ → Option (Q × List Γ)
  det : ∀ q Z, (trans q none Z).isSome → ∀ a, trans q (some a) Z = none

namespace DPDA

variable {Q : Type u} {Γ : Type v} {σ : Type w} (M : DPDA Q Γ σ)

/-- Configurations: control state, unread input, stack (head = top). -/
abbrev Config (Q : Type u) (Γ : Type v) (σ : Type w) := Q × List σ × List Γ

/-- One move of `M`. -/
inductive Step : Config Q Γ σ → Config Q Γ σ → Prop
  | read {q q' : Q} {a : σ} {w : List σ} {Z : Γ} {γ st : List Γ}
      (h : M.trans q (some a) Z = some (q', γ)) :
      Step (q, a :: w, Z :: st) (q', w, γ ++ st)
  | eps {q q' : Q} {w : List σ} {Z : Γ} {γ st : List Γ}
      (h : M.trans q none Z = some (q', γ)) :
      Step (q, w, Z :: st) (q', w, γ ++ st)

/-- Finitely many moves. -/
def Reaches : Config Q Γ σ → Config Q Γ σ → Prop :=
  Relation.ReflTransGen M.Step

/-- Acceptance by final state. -/
def Accepts (w : List σ) : Prop :=
  ∃ q st, M.Reaches (M.start, w, [M.bottom]) (q, [], st) ∧ M.final q

/-- The language of `M`. -/
def language : Set (List σ) := {w | M.Accepts w}

/-- **Determinism**: every configuration has at most one successor. -/
theorem step_deterministic {c c₁ c₂ : Config Q Γ σ}
    (h₁ : M.Step c c₁) (h₂ : M.Step c c₂) : c₁ = c₂ := by
  cases h₁ with
  | @read q q₁ a w Z γ₁ st t₁ =>
      cases h₂ with
      | read t₂ =>
          rw [t₁] at t₂
          cases t₂
          rfl
      | eps t₂ =>
          have := M.det q Z (by rw [t₂]; rfl) a
          rw [this] at t₁
          cases t₁
  | @eps q q₁ w Z γ₁ st t₁ =>
      cases h₂ with
      | @read _ _ a' _ _ _ _ t₂ =>
          have := M.det q Z (by rw [t₁]; rfl) a'
          rw [this] at t₂
          cases t₂
      | eps t₂ =>
          rw [t₁] at t₂
          cases t₂
          rfl

/-- A DPDA without ε-moves (real-time). -/
def RealTime : Prop := ∀ q Z, M.trans q none Z = none

/-- The deterministic run of a real-time DPDA, one input symbol per move. -/
def run : Q → List Γ → List σ → Option (Q × List Γ)
  | q, st, [] => some (q, st)
  | _, [], _ :: _ => none
  | q, Z :: st, a :: w =>
      match M.trans q (some a) Z with
      | none => none
      | some (q', γ) => run q' (γ ++ st) w

theorem step_of_realTime (hrt : M.RealTime) {c c' : Config Q Γ σ} (h : M.Step c c') :
    ∃ q q' a w Z γ st, c = (q, a :: w, Z :: st) ∧ c' = (q', w, γ ++ st) ∧
      M.trans q (some a) Z = some (q', γ) := by
  cases h with
  | read t => exact ⟨_, _, _, _, _, _, _, rfl, rfl, t⟩
  | eps t => rw [hrt] at t; cases t

/-- For a real-time DPDA, consuming the whole input by moves is the run function. -/
theorem reaches_iff_run (hrt : M.RealTime) (q : Q) (st : List Γ) (w : List σ)
    (q' : Q) (st' : List Γ) :
    M.Reaches (q, w, st) (q', [], st') ↔ M.run q st w = some (q', st') := by
  induction w generalizing q st with
  | nil =>
      constructor
      · intro h
        rcases Relation.ReflTransGen.cases_head h with he | ⟨c, hs, _⟩
        · cases he; rfl
        · obtain ⟨_, _, _, _, _, _, _, he, _, _⟩ := M.step_of_realTime hrt hs
          cases he
      · intro h
        cases h
        exact Relation.ReflTransGen.refl
  | cons a w ih =>
      constructor
      · intro h
        rcases Relation.ReflTransGen.cases_head h with he | ⟨c, hs, hrest⟩
        · cases he
        · obtain ⟨q0, q1, a0, w0, Z, γ, st0, he, rfl, ht⟩ := M.step_of_realTime hrt hs
          simp only [Prod.mk.injEq, List.cons.injEq] at he
          obtain ⟨rfl, ⟨rfl, rfl⟩, rfl⟩ := he
          have hrest' : M.Reaches (q1, w, γ ++ st0) (q', [], st') := hrest
          rw [ih] at hrest'
          show (match M.trans q (some a) Z with
            | none => none
            | some (q', γ) => M.run q' (γ ++ st0) w) = _
          rw [ht]
          exact hrest'
      · intro h
        cases st with
        | nil => cases h
        | cons Z st =>
            have h' : (match M.trans q (some a) Z with
                | none => none
                | some (q', γ) => M.run q' (γ ++ st) w) = some (q', st') := h
            cases ht : M.trans q (some a) Z with
            | none => rw [ht] at h'; cases h'
            | some p =>
                obtain ⟨q1, γ⟩ := p
                rw [ht] at h'
                exact Relation.ReflTransGen.head (Step.read ht) ((ih q1 (γ ++ st)).mpr h')

/-- Acceptance of a real-time DPDA through its run function. -/
theorem accepts_iff_run (hrt : M.RealTime) (w : List σ) :
    M.Accepts w ↔ ∃ q st, M.run M.start [M.bottom] w = some (q, st) ∧ M.final q := by
  unfold Accepts
  constructor
  · rintro ⟨q, st, h, hf⟩
    exact ⟨q, st, (M.reaches_iff_run hrt _ _ _ _ _).mp h, hf⟩
  · rintro ⟨q, st, h, hf⟩
    exact ⟨q, st, (M.reaches_iff_run hrt _ _ _ _ _).mpr h, hf⟩

end DPDA

/--
`L` is deterministic context-free: some DPDA with finitely many control states
and finitely many stack symbols accepts exactly `L` (by final state).
-/
def IsDCFL {σ : Type w} (L : Set (List σ)) : Prop :=
  ∃ (Q : Type) (Γ : Type) (_ : Fintype Q) (_ : Fintype Γ) (M : DPDA Q Γ σ),
    M.language = L

end TCS1
end LeanCfgProject
