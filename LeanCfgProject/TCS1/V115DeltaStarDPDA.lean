import LeanCfgProject.TCS1.DeltaStarFixedWindow

/-!
# TCS #1 v115: explicit deterministic pushdown recognizer for Delta-star

The v115 manuscript calls Delta-star deterministic context-free.
Unlike the earlier Mode-based reference scanner (with an unbounded
natural-number counter), this file gives an *explicit pushdown machine*
with two finite control states and a one-symbol stack alphabet (and an
implicit bottom marker).

Its transition instruction depends ONLY on:
  current finite control, current top-of-stack (or bottom), input letter.
Every enabled transition consumes exactly one input symbol; there are
no epsilon transitions or transition choices.  The "push" action
increments a physical stack and the "pop" action removes one stack
symbol.  The falling state with an empty stack marks a completed block.

We verify its behavior step by step against the previously proved
reference scan, so the accepted language is exactly DeltaStar.Language.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/-- The finite control, independent of the unbounded stack. -/
inductive DPDAControl where
  | rising
  | falling
  deriving DecidableEq, Fintype, Repr

/-- All stack symbols are identical, with the bottom represented by []. -/
abbrev DPDAStack := List Unit

/-- Standard push/pop instructions, not a whole-stack lookahead. -/
inductive DPDAAction where
  | push
  | pop
  deriving DecidableEq, Repr

/--
This transition table reads the control, the top symbol/bottom marker
and one input letter.  It never examines the rest of the stack.
-/
def dpdaInstruction :
    DPDAControl → Option Unit → Symbol →
      Option (DPDAControl × DPDAAction)
  | .rising, _, .a => some (.rising, .push)
  | .rising, some (), .b => some (.falling, .pop)
  | .rising, none, .b => none
  | .falling, none, .a => some (.rising, .push)
  | .falling, some (), .a => none
  | .falling, some (), .b => some (.falling, .pop)
  | .falling, none, .b => none

abbrev DPDAConfiguration := DPDAControl × DPDAStack

/-- Execute the unique enabled action (if any). -/
def dpdaStep :
    DPDAConfiguration → Symbol → Option DPDAConfiguration
  | (mode, stack), s =>
      match dpdaInstruction mode stack.head? s with
      | none => none
      | some (next, .push) => some (next, () :: stack)
      | some (next, .pop) =>
          match stack with
          | [] => none
          | _ :: rest => some (next, rest)

/-- The one-step transition relation of the concrete pushdown machine. -/
def DPDATransition
    (c : DPDAConfiguration)
    (s : Symbol)
    (d : DPDAConfiguration) : Prop :=
  dpdaStep c s = some d

/-- Determinism, proved from the actual transition relation. -/
theorem dpda_transition_unique
    {c d e : DPDAConfiguration}
    {s : Symbol}
    (hd : DPDATransition c s d)
    (he : DPDATransition c s e) :
    d = e := by
  exact Option.some.inj (hd.symm.trans he)

/-- Input-consuming execution without epsilon moves. -/
def dpdaRun :
    DPDAConfiguration → Word Symbol →
      Option DPDAConfiguration
  | c, [] => some c
  | c, a :: w =>
      match dpdaStep c a with
      | none => none
      | some d => dpdaRun d w

/--
Encode the three reference scanner modes using physical stacks.
Each positive mode n carries n+1 real stack symbols; zero is the
falling control at the bottom marker.
-/
def dpdaEncode : Mode → DPDAConfiguration
  | .zero => (.falling, [])
  | .rising n => (.rising, List.replicate (n + 1) ())
  | .falling n => (.falling, List.replicate (n + 1) ())

/-- The finite-control pushdown step simulates the reference step. -/
theorem dpda_step_encode
    (q : Mode)
    (a : Symbol) :
    dpdaStep (dpdaEncode q) a =
      (step q a).map dpdaEncode := by
  cases q with
  | zero =>
      cases a <;>
        simp [dpdaStep, dpdaEncode, dpdaInstruction, step]
  | rising n =>
      cases n with
      | zero =>
          cases a <;>
            simp [dpdaStep, dpdaEncode, dpdaInstruction,
              step, List.replicate_succ]
      | succ n =>
          cases a <;>
            simp [dpdaStep, dpdaEncode, dpdaInstruction,
              step, List.replicate_succ]
  | falling n =>
      cases n with
      | zero =>
          cases a <;>
            simp [dpdaStep, dpdaEncode, dpdaInstruction,
              step, List.replicate_succ]
      | succ n =>
          cases a <;>
            simp [dpdaStep, dpdaEncode, dpdaInstruction,
              step, List.replicate_succ]

/-- The simulation extends to every complete input word. -/
theorem dpda_run_encode
    (q : Mode)
    (w : Word Symbol) :
    dpdaRun (dpdaEncode q) w =
      (scan q w).map dpdaEncode := by
  induction w generalizing q with
  | nil =>
      rfl
  | cons a w ih =>
      simp only [dpdaRun, scan, dpda_step_encode]
      cases hs : step q a with
      | none =>
          simp [hs]
      | some q' =>
          simpa [hs] using ih q'

/-- Acceptance at the initial and final bottom-stack configuration. -/
def DPDALanguage : Set (Word Symbol) :=
  {w | dpdaRun (.falling, []) w = some (.falling, [])}

/--
The concrete deterministic pushdown machine recognizes Delta-star,
not merely a superset or an abstract grammar encoding.
-/
theorem dpda_language_eq : DPDALanguage = Language := by
  apply Set.ext
  intro w
  change
    dpdaRun (dpdaEncode .zero) w =
        some (dpdaEncode .zero) ↔
      scan .zero w = some .zero
  rw [dpda_run_encode]
  cases hs : scan .zero w with
  | none =>
      simp [hs]
  | some q =>
      cases q with
      | zero =>
          simp [hs]
      | rising n =>
          simp [hs, dpdaEncode]
      | falling n =>
          simp [hs, dpdaEncode, List.replicate_succ]

/-- Paper-facing deterministic-context-free assertion as an explicit DPDA. -/
theorem deltaStar_deterministic_pushdown :
    (∀ (c d e : DPDAConfiguration) (a : Symbol),
      DPDATransition c a d →
      DPDATransition c a e →
      d = e)
      ∧
    DPDALanguage = Language := by
  exact ⟨fun c d e a hd he => dpda_transition_unique hd he,
    dpda_language_eq⟩

end DeltaStar
end TCS1
end LeanCfgProject
