import Mathlib.Computability.DFA
import LeanCfgProject.TCS1.CappedCounterFixedWindow
import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v78: finite-state / fixed-h witness for the capped counter

This module supplies the positive half of the regular-separation example from
Section 9.  The capped counter has finitely many live heights 0,...,rho plus
one sink state.  Every word acts on this finite state set, so the induced
transition monoid gives an explicit finite-monoid homomorphism recognizing
the language.

Combining this witness with CappedCounter.not_fixedWindowSubstitutable
yields the paper's semantic separation: for every rho >= 2 the capped counter
is fixed-h substitutable for a concrete finite h, but lies outside every
fixed prefix-suffix window class.
-/

namespace LeanCfgProject
namespace TCS1
namespace CappedCounter

/-- Live counter heights 0,...,rho plus a sink state represented by none. -/
abbrev State (rho : Nat) :=
  Option (Fin (rho + 1))

/-- Initial live height 0. -/
def initialState
    (rho : Nat) :
    State rho :=
  some ⟨0, Nat.succ_pos rho⟩

/-- Forget the finite proof and expose the optional numerical height. -/
def stateHeight
    {rho : Nat} :
    State rho → Option Nat
  | none => none
  | some h => some h.1

/-- One finite-state transition.  The sink is absorbing. -/
def step
    (rho : Nat) :
    State rho → Symbol → State rho
  | none, _ => none
  | some h, .reset =>
      initialState rho
  | some h, .up =>
      if hh : h.1 < rho then
        some ⟨h.1 + 1, by omega⟩
      else
        none
  | some h, .down =>
      if hh : 0 < h.1 then
        some ⟨h.1 - 1, by
          have hlt : h.1 < rho + 1 := h.2
          omega⟩
      else
        none

/-- Run the finite capped-counter automaton from an arbitrary state. -/
def run
    (rho : Nat) :
    State rho → Word Symbol → State rho
  | q, [] => q
  | q, s :: w =>
      run rho (step rho q s) w

/-- Once the automaton reaches the sink, every suffix stays in the sink. -/
@[simp] theorem run_none
    (rho : Nat)
    (w : Word Symbol) :
    run rho none w = none := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      simpa [run, step] using ih

/-- Word actions compose across concatenation. -/
theorem run_append
    (rho : Nat)
    (q : State rho)
    (u v : Word Symbol) :
    run rho q (u ++ v) =
      run rho (run rho q u) v := by
  induction u generalizing q with
  | nil =>
      rfl
  | cons s u ih =>
      simp only [List.cons_append, run]
      exact ih (q := step rho q s)

/--
The finite-state run has exactly the same optional height as the semantic
scanner from the capped-counter module.
-/
theorem stateHeight_run
    (rho : Nat)
    (q : State rho)
    (w : Word Symbol) :
    stateHeight (run rho q w) =
      match q with
      | none => none
      | some h => scan rho h.1 w := by
  induction w generalizing q with
  | nil =>
      cases q <;> rfl
  | cons s w ih =>
      cases q with
      | none =>
          simp [run, step, run_none, stateHeight]
      | some h =>
          cases s with
          | reset =>
              simpa [run, step, scan,
                initialState, stateHeight] using
                ih (q := initialState rho)
          | up =>
              by_cases hh : h.1 < rho
              · let h' : Fin (rho + 1) :=
                  ⟨h.1 + 1, by omega⟩
                have hi :=
                  ih (q := some h')
                simpa [run, step, scan, hh,
                  h', stateHeight] using hi
              · simp [run, step, scan, hh,
                  run_none, stateHeight]
          | down =>
              cases h with
              | mk hv hlt =>
                  cases hv with
                  | zero =>
                      simp [run, step, scan,
                        run_none, stateHeight]
                  | succ hv =>
                      let h' : Fin (rho + 1) :=
                        ⟨hv, by omega⟩
                      have hi :=
                        ih (q := some h')
                      simpa [run, step, scan,
                        h', stateHeight] using hi

/-- A finite transformation of the capped-counter state set. -/
structure Transition (rho : Nat) where
  toFun : State rho → State rho
  deriving Fintype

@[ext] theorem Transition.ext
    {rho : Nat}
    {f g : Transition rho}
    (h : ∀ q, f.toFun q = g.toFun q) :
    f = g := by
  cases f with
  | mk ff =>
      cases g with
      | mk gg =>
          congr
          funext q
          exact h q

/--
Composition order follows word reading: f * g means first apply f, then g.
-/
instance transitionMonoid
    (rho : Nat) :
    Monoid (Transition rho) where
  one :=
    ⟨fun q => q⟩
  mul f g :=
    ⟨fun q => g.toFun (f.toFun q)⟩
  one_mul f := by
    apply Transition.ext
    intro q
    rfl
  mul_one f := by
    apply Transition.ext
    intro q
    rfl
  mul_assoc f g h := by
    apply Transition.ext
    intro q
    rfl

/-- Transition induced by one whole word. -/
def wordTransition
    (rho : Nat)
    (w : Word Symbol) :
    Transition rho :=
  ⟨fun q => run rho q w⟩

/-- Explicit transition-monoid homomorphism for the capped counter. -/
def transitionMonoidHom
    (rho : Nat) :
    FixedFiniteMonoidHom
      Symbol (Transition rho) where
  h := wordTransition rho
  map_nil := by
    apply Transition.ext
    intro q
    rfl
  map_append := by
    intro u v
    apply Transition.ext
    intro q
    exact run_append rho q u v

/-- Accepting transformations are those that keep the initial state live. -/
def acceptingTransitions
    (rho : Nat) :
    Set (Transition rho) :=
  {t | t.toFun (initialState rho) ≠ none}

/--
The scanner language is exactly the preimage recognized by the transition
monoid.
-/
theorem language_eq_recognizedPreimage
    (rho : Nat) :
    Language rho =
      RecognizedPreimage
        (transitionMonoidHom rho)
        (acceptingTransitions rho) := by
  apply Set.ext
  intro w
  have hrel :=
    stateHeight_run
      rho (initialState rho) w
  have hrel' :
      stateHeight
          (run rho (initialState rho) w) =
        scan rho 0 w := by
    simpa [initialState, stateHeight] using hrel
  constructor
  · rintro ⟨h, hscan⟩
    change
      run rho (initialState rho) w ≠ none
    intro hnone
    rw [hnone] at hrel'
    simp [stateHeight, hscan] at hrel'
  · intro hrun
    change
      run rho (initialState rho) w ≠ none at hrun
    cases hr :
        run rho (initialState rho) w with
    | none =>
        exact False.elim (hrun hr)
    | some q =>
        refine ⟨q.1, ?_⟩
        rw [hr] at hrel'
        simpa [stateHeight] using hrel'.symm

/--
Concrete fixed-h substitutability witness for every capped-counter language.
-/
theorem fixedHSubstitutable_transitionMonoid
    (rho : Nat) :
    FixedHSubstitutable
      (transitionMonoidHom rho)
      (Language rho) := by
  rw [language_eq_recognizedPreimage rho]
  exact
    recognizedPreimage_fixedHSubstitutable
      (transitionMonoidHom rho)
      (acceptingTransitions rho)

/-- The capped-counter language viewed through Mathlib's formal-language API. -/
def FormalLanguage
    (rho : Nat) :
    _root_.Language Symbol :=
  {w | w ∈ Language rho}

/-- DFA with live heights as accepting states and the overflow/underflow sink rejecting. -/
def automaton
    (rho : Nat) :
    DFA Symbol (State rho) where
  step := step rho
  start := initialState rho
  accept := {q | q ≠ none}

/-- Mathlib DFA evaluation coincides with the recursive finite-state run. -/
theorem automaton_evalFrom_eq_run
    (rho : Nat)
    (q : State rho)
    (w : Word Symbol) :
    (automaton rho).evalFrom q w =
      run rho q w := by
  induction w generalizing q with
  | nil =>
      rfl
  | cons s w ih =>
      rw [DFA.evalFrom_cons]
      change
        (automaton rho).evalFrom
            (step rho q s) w =
          run rho (step rho q s) w
      exact ih (q := step rho q s)

/-- Evaluation from the DFA start state is the capped-counter run from height zero. -/
theorem automaton_eval_eq_run
    (rho : Nat)
    (w : Word Symbol) :
    (automaton rho).eval w =
      run rho (initialState rho) w := by
  change
    (automaton rho).evalFrom
        (initialState rho) w =
      run rho (initialState rho) w
  exact
    automaton_evalFrom_eq_run
      rho (initialState rho) w

/-- The explicit DFA accepts exactly the semantic capped-counter language. -/
theorem automaton_accepts_eq
    (rho : Nat) :
    (automaton rho).accepts =
      FormalLanguage rho := by
  apply Set.ext
  intro w
  change
    (automaton rho).eval w ≠ none ↔
      ∃ h : Nat, scan rho 0 w = some h
  rw [automaton_eval_eq_run]
  have hrel :=
    stateHeight_run
      rho (initialState rho) w
  have hrel' :
      stateHeight
          (run rho (initialState rho) w) =
        scan rho 0 w := by
    simpa [initialState, stateHeight] using hrel
  constructor
  · intro hrun
    cases hr :
        run rho (initialState rho) w with
    | none =>
        exact False.elim (hrun hr)
    | some q =>
        refine ⟨q.1, ?_⟩
        rw [hr] at hrel'
        simpa [stateHeight] using hrel'.symm
  · rintro ⟨h, hscan⟩ hrun
    rw [hrun] at hrel'
    simp [stateHeight, hscan] at hrel'

/-- Proposition 9 regularity component: every capped-counter language is regular. -/
theorem isRegular
    (rho : Nat) :
    (FormalLanguage rho).IsRegular := by
  rw [_root_.Language.isRegular_iff]
  exact
    ⟨State rho,
      inferInstance,
      automaton rho,
      automaton_accepts_eq rho⟩

/--
Paper-facing regular/fixed-h package for the capped counter.  The regularity
proof uses the same rho+2-state automaton whose transition monoid supplies the
fixed-h witness.
-/
theorem regular_and_fixedH
    (rho : Nat) :
    (FormalLanguage rho).IsRegular
      ∧
    FixedHSubstitutable
      (transitionMonoidHom rho)
      (Language rho) := by
  exact
    ⟨isRegular rho,
      fixedHSubstitutable_transitionMonoid rho⟩

/--
Paper-facing regular-separation core: for rho >= 2, the same capped-counter
language is fixed-h substitutable for an explicit finite transition monoid,
yet it is not (k,l)-substitutable for the arbitrary fixed window.
-/
theorem fixedH_but_not_fixedWindow
    (rho : Nat)
    (hrho : 2 ≤ rho)
    (k l : Nat) :
    FixedHSubstitutable
        (transitionMonoidHom rho)
        (Language rho)
      ∧
    ¬ FixedWindowSubstitutable
        k l (Language rho) := by
  exact
    ⟨fixedHSubstitutable_transitionMonoid rho,
      not_fixedWindowSubstitutable
        rho hrho k l⟩

end CappedCounter
end TCS1
end LeanCfgProject
