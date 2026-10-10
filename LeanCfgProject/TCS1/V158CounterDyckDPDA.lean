import LeanCfgProject.TCS1.V158DPDA
import LeanCfgProject.TCS1.UncappedCounterObstruction
import LeanCfgProject.TCS1.DyckOneBracketKernel

/-!
# TCS #1 v158: DPDAs for the uncapped counter `CTR` and the Dyck language `D₁`

Section `sec:outside-rs` of the manuscript calls `CTR` "the deterministic
context-free language … accepted by the evident deterministic pushdown counter
with reset" and `D₁` "a standard deterministic context-free language".  These
are prose remarks (not numbered claims); with the general `DPDA` model they are
proved here for the languages already used in Lean (`UncappedCounter.Language`,
`DyckOne.Language`).

* `counterDPDA` (one control state, real-time): `↑` pushes a counter cell,
  `↓` pops one (undefined on a bottom marker = underflow), `reset` pushes a
  fresh bottom marker, so the counter value is the number of cells above the
  top-most marker.  Every state is final: a word is accepted iff no underflow
  occurs.
* `dyckDPDA` (states `bal`/`pos`, real-time): the same `first`/`mark` device as
  for `Δ*`; `bal` (height 0) is the only final state.
-/

namespace LeanCfgProject
namespace TCS1

/-! ### Uncapped counter -/

namespace UncappedCounter

open Symbol

inductive CStack where
  | bot
  | cell
  deriving DecidableEq, Fintype, Repr

def cTrans : Unit → Option Symbol → CStack → Option (Unit × List CStack)
  | (), some up, Z => some ((), [.cell, Z])
  | (), some down, .cell => some ((), [])
  | (), some reset, Z => some ((), [.bot, Z])
  | _, _, _ => none

def counterDPDA : DPDA Unit CStack Symbol where
  start := ()
  bottom := .bot
  final _ := True
  trans := cTrans
  det q Z h _ := by cases q <;> cases Z <;> simp [cTrans] at h

theorem counterDPDA_realTime : counterDPDA.RealTime := by
  intro q Z; cases q; cases Z <;> rfl

theorem counter_run_isSome (w : Word Symbol) :
    ∀ (h : Nat) (rest : List CStack),
      (counterDPDA.run () (List.replicate h .cell ++ CStack.bot :: rest) w).isSome =
        (scan h w).isSome := by
  induction w with
  | nil => intro h rest; rfl
  | cons s w ih =>
      intro h rest
      cases s with
      | up =>
          have := ih (h + 1) rest
          rw [List.replicate_succ] at this
          cases h <;> exact this
      | down =>
          cases h with
          | zero => rfl
          | succ h =>
              rw [List.replicate_succ]
              exact ih h rest
      | reset =>
          have := ih 0 (List.replicate h .cell ++ CStack.bot :: rest)
          cases h <;> exact this

theorem counterDPDA_language : counterDPDA.language = Language := by
  ext w
  show counterDPDA.Accepts w ↔ ∃ h : Nat, scan 0 w = some h
  rw [DPDA.accepts_iff_run _ counterDPDA_realTime]
  have key := counter_run_isSome w 0 []
  simp only [List.replicate_zero, List.nil_append] at key
  constructor
  · rintro ⟨q, st, hr, _⟩
    have : (counterDPDA.run () [CStack.bot] w).isSome := by
      show (counterDPDA.run counterDPDA.start [counterDPDA.bottom] w).isSome
      rw [hr]; rfl
    rw [key] at this
    exact Option.isSome_iff_exists.mp this
  · rintro ⟨h, hs⟩
    have : (counterDPDA.run () [CStack.bot] w).isSome := by rw [key, hs]; rfl
    obtain ⟨⟨q, st⟩, hr⟩ := Option.isSome_iff_exists.mp this
    exact ⟨q, st, hr, trivial⟩

/-- **`CTR` is deterministic context-free.** -/
theorem uncappedCounter_isDCFL : IsDCFL Language :=
  ⟨Unit, CStack, inferInstance, inferInstance, counterDPDA, counterDPDA_language⟩

end UncappedCounter

/-! ### One-bracket Dyck language -/

namespace DyckOne

open Symbol

inductive YState where
  | bal
  | pos
  deriving DecidableEq, Fintype, Repr

inductive YStack where
  | bot
  | first
  | mark
  deriving DecidableEq, Fintype, Repr

def yTrans : YState → Option Symbol → YStack → Option (YState × List YStack)
  | .bal, some a, .bot => some (.pos, [.first, .bot])
  | .pos, some a, .first => some (.pos, [.mark, .first])
  | .pos, some a, .mark => some (.pos, [.mark, .mark])
  | .pos, some b, .mark => some (.pos, [])
  | .pos, some b, .first => some (.bal, [])
  | _, _, _ => none

def dyckDPDA : DPDA YState YStack Symbol where
  start := .bal
  bottom := .bot
  final q := q = .bal
  trans := yTrans
  det q Z h _ := by cases q <;> cases Z <;> simp [yTrans] at h

theorem dyckDPDA_realTime : dyckDPDA.RealTime := by
  intro q Z; cases q <;> cases Z <;> rfl

def yEncode : Nat → YState × List YStack
  | 0 => (.bal, [.bot])
  | n + 1 => (.pos, List.replicate n .mark ++ [.first, .bot])

theorem dyck_run_encode (w : Word Symbol) :
    ∀ h : Nat, dyckDPDA.run (yEncode h).1 (yEncode h).2 w = (scan h w).map yEncode := by
  induction w with
  | nil => intro h; rfl
  | cons s w ih =>
      intro h
      cases s with
      | a =>
          have := ih (h + 1)
          rcases h with _ | _ | h <;> exact this
      | b =>
          cases h with
          | zero => rfl
          | succ h =>
              have := ih h
              cases h with
              | zero => exact this
              | succ h => exact this

theorem dyckDPDA_language : dyckDPDA.language = Language := by
  ext w
  show dyckDPDA.Accepts w ↔ scan 0 w = some 0
  rw [DPDA.accepts_iff_run _ dyckDPDA_realTime]
  have key := dyck_run_encode w 0
  change dyckDPDA.run YState.bal [YStack.bot] w = _ at key
  show (∃ q st, dyckDPDA.run YState.bal [YStack.bot] w = some (q, st) ∧ q = YState.bal) ↔ _
  rw [key]
  constructor
  · rintro ⟨q, st, hq, rfl⟩
    cases hs : scan 0 w with
    | none => rw [hs] at hq; cases hq
    | some m =>
        rw [hs] at hq
        simp only [Option.map_some, Option.some.injEq] at hq
        cases m with
        | zero => rfl
        | succ m => simp [yEncode] at hq
  · intro hs
    rw [hs]
    exact ⟨.bal, [.bot], rfl, rfl⟩

/-- **`D₁` is deterministic context-free.** -/
theorem dyckOne_isDCFL : IsDCFL Language :=
  ⟨YState, YStack, inferInstance, inferInstance, dyckDPDA, dyckDPDA_language⟩

end DyckOne

end TCS1
end LeanCfgProject
