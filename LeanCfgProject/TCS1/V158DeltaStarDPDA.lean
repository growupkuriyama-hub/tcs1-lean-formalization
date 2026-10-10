import LeanCfgProject.TCS1.V158DPDA
import LeanCfgProject.TCS1.DeltaStarFixedWindow

/-!
# TCS #1 v158: an explicit DPDA for `Δ*` (`prop:nonlinear-rs-example`, DCFL clause)

The manuscript (v158, proof of `prop:nonlinear-rs-example`): "a DPDA pushes
while reading the `a`-part of a factor `aⁿbⁿ`, pops during its `b`-part, and
permits a new such factor only after the stack returns to its bottom marker."

**Machine `deltaStarDPDA`** (real-time: no ε-moves).
* control states `ready` (between blocks; the only final state), `up` (reading
  the `a`-part), `down` (reading the `b`-part);
* stack symbols `bot` (initial bottom marker), `first` (the counter cell of the
  first `a` of the current block, placed directly on `bot`), `mark` (the
  counter cells of the further `a`s);
* moves:
  - `ready, a, bot ↦ up, first bot` (start a block),
  - `up, a, Z ↦ up, mark Z` for `Z ∈ {first, mark}` (push),
  - `up/down, b, mark ↦ down, ε` (pop),
  - `up/down, b, first ↦ ready, ε` (pop the last cell: the stack is back at `bot`),
  - all other moves are undefined (reject): `b` at the bottom marker, and `a`
    during a `b`-part.

The separate cell type `first` lets the finite control know when the stack has
returned to its bottom marker without an ε-move, so acceptance by the final
state `ready` is exact.

Results:
* `deltaStarDPDA_realTime`; determinism is part of `DPDA` (`DPDA.step_deterministic`);
* `run_encode` (simulation of the existing parser `scan`, step by step);
* `stack_length_eq` (stack invariant: after reading a prefix `u` the stack
  height above the bottom marker is the number of unmatched `a`s,
  `|u|_a − |u|_b`);
* `deltaStarDPDA_accepts_iff_scan`, `deltaStarDPDA_language`
  (`L(DPDA) = DeltaStar.Language`);
* `deltaStar_isDCFL`.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/-- Control states. -/
inductive DState where
  | ready
  | up
  | down
  deriving DecidableEq, Fintype, Repr

/-- Stack symbols. -/
inductive DStack where
  | bot
  | first
  | mark
  deriving DecidableEq, Fintype, Repr

/-- The transition function. -/
def dTrans : DState → Option Symbol → DStack → Option (DState × List DStack)
  | .ready, some a, .bot => some (.up, [.first, .bot])
  | .up, some a, .first => some (.up, [.mark, .first])
  | .up, some a, .mark => some (.up, [.mark, .mark])
  | .up, some b, .mark => some (.down, [])
  | .up, some b, .first => some (.ready, [])
  | .down, some b, .mark => some (.down, [])
  | .down, some b, .first => some (.ready, [])
  | _, _, _ => none

/-- The DPDA for `Δ*`. -/
def deltaStarDPDA : DPDA DState DStack Symbol where
  start := .ready
  bottom := .bot
  final q := q = .ready
  trans := dTrans
  det q Z h _ := by cases q <;> cases Z <;> simp [dTrans] at h

theorem deltaStarDPDA_realTime : deltaStarDPDA.RealTime := by
  intro q Z
  cases q <;> cases Z <;> rfl

/-- Encoding of the parser modes as DPDA configurations. -/
def encode : Mode → DState × List DStack
  | .zero => (.ready, [.bot])
  | .rising n => (.up, List.replicate n .mark ++ [.first, .bot])
  | .falling n => (.down, List.replicate n .mark ++ [.first, .bot])

/-- One input symbol: the DPDA move simulates `step`. -/
theorem run_cons_encode (m : Mode) (s : Symbol) (w : Word Symbol) :
    deltaStarDPDA.run (encode m).1 (encode m).2 (s :: w) =
      match step m s with
      | none => none
      | some m' => deltaStarDPDA.run (encode m').1 (encode m').2 w := by
  cases m with
  | zero => cases s <;> rfl
  | rising n =>
      cases n with
      | zero => cases s <;> rfl
      | succ n => cases s <;> rfl
  | falling n =>
      cases n with
      | zero => cases s <;> rfl
      | succ n => cases s <;> rfl

/-- **Simulation**: the DPDA run is the encoded parser run. -/
theorem run_encode (m : Mode) (w : Word Symbol) :
    deltaStarDPDA.run (encode m).1 (encode m).2 w = (scan m w).map encode := by
  induction w generalizing m with
  | nil => rfl
  | cons s w ih =>
      rw [run_cons_encode]
      show _ = (match step m s with
        | none => none
        | some m' => scan m' w).map encode
      cases step m s with
      | none => rfl
      | some m' => exact ih m'

theorem encode_final_iff (m : Mode) : (encode m).1 = .ready ↔ m = .zero := by
  cases m <;> simp [encode]

/-- **Acceptance agrees with the existing deterministic parser.** -/
theorem deltaStarDPDA_accepts_iff_scan (w : Word Symbol) :
    deltaStarDPDA.Accepts w ↔ scan .zero w = some .zero := by
  rw [DPDA.accepts_iff_run _ deltaStarDPDA_realTime]
  have h := run_encode .zero w
  change deltaStarDPDA.run DState.ready [DStack.bot] w = _ at h
  show (∃ q st, deltaStarDPDA.run DState.ready [DStack.bot] w = some (q, st) ∧
      q = DState.ready) ↔ _
  rw [h]
  constructor
  · rintro ⟨q, st, hq, rfl⟩
    cases hs : scan .zero w with
    | none => rw [hs] at hq; cases hq
    | some m =>
        rw [hs] at hq
        simp only [Option.map_some, Option.some.injEq] at hq
        have : (encode m).1 = .ready := by rw [hq]
        rw [(encode_final_iff m).mp this]
  · intro hs
    rw [hs]
    exact ⟨.ready, [.bot], rfl, rfl⟩

/-- **The DPDA accepts exactly `DeltaStar.Language`.** -/
theorem deltaStarDPDA_language : deltaStarDPDA.language = Language := by
  ext w
  exact deltaStarDPDA_accepts_iff_scan w

/-- **`Δ*` is deterministic context-free** (DPDA semantics). -/
theorem deltaStar_isDCFL : IsDCFL Language :=
  ⟨DState, DStack, inferInstance, inferInstance, deltaStarDPDA, deltaStarDPDA_language⟩

/-! ### Stack invariant -/

/-- Number of unmatched `a`s recorded by a parser mode. -/
def pending : Mode → Nat
  | .zero => 0
  | .rising n => n + 1
  | .falling n => n + 1

theorem encode_stack_length (m : Mode) : (encode m).2.length = pending m + 1 := by
  cases m <;> simp [encode, pending]

theorem pending_step {m m' : Mode} {s : Symbol} (h : step m s = some m') :
    (pending m' : Int) = pending m + (if s = a then 1 else -1) := by
  cases m with
  | zero => cases s <;> simp [step] at h <;> subst h <;> simp [pending]
  | rising n =>
      cases n <;> cases s <;> simp [step] at h <;> subst h <;> simp [pending] <;> omega
  | falling n =>
      cases n <;> cases s <;> simp [step] at h <;> subst h <;> simp [pending] <;> omega

theorem pending_scan :
    ∀ (w : Word Symbol) (m m' : Mode), scan m w = some m' →
      (pending m' : Int) = pending m + (w.count a : Int) - (w.count b : Int)
  | [], m, m', h => by
      simp only [scan, Option.some.injEq] at h
      subst h; simp
  | s :: w, m, m', h => by
      have h' : (match step m s with
          | none => none
          | some m'' => scan m'' w) = some m' := h
      cases hs : step m s with
      | none => rw [hs] at h'; cases h'
      | some m'' =>
          rw [hs] at h'
          have e1 := pending_scan w m'' m' h'
          have e2 := pending_step hs
          cases s <;> simp [List.count_cons] at e2 ⊢ <;> omega

/--
**Stack invariant.**  If the DPDA has read a prefix `u` (without rejecting),
its stack has height `1 + (|u|_a − |u|_b)`: the bottom marker plus one cell for
each unmatched `a` of the current block.
-/
theorem stack_length_eq (u : Word Symbol) (q : DState) (st : List DStack)
    (h : deltaStarDPDA.run .ready [.bot] u = some (q, st)) :
    (st.length : Int) = 1 + (u.count a : Int) - (u.count b : Int) := by
  have hr := run_encode .zero u
  change deltaStarDPDA.run DState.ready [DStack.bot] u = _ at hr
  rw [hr] at h
  cases hs : scan .zero u with
  | none => rw [hs] at h; cases h
  | some m =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq] at h
      have e1 : st.length = pending m + 1 := by rw [← encode_stack_length m, h]
      have e2 := pending_scan u .zero m hs
      have e3 : ((pending Mode.zero : Nat) : Int) = 0 := rfl
      have e4 : ((st.length : Nat) : Int) = (pending m : Int) + 1 := by exact_mod_cast e1
      rw [e3] at e2
      rw [e4, e2]
      ring

end DeltaStar
end TCS1
end LeanCfgProject
