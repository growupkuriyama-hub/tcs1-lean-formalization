import LeanCfgProject.TCS1.BinaryMembershipChart

/-!
# TCS #1 v79: executable terminal seed for the CYK chart

For an input word w of length n, the initial chart scans the finite candidate
space N x Fin n.  Candidate (A,i) inserts the unit span (A,i,i+1) exactly when
the grammar contains A -> w[i].

This is the executable terminal layer of the internal membership test.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryMembershipSeed

variable {N : Type u}
variable {α : Type v}

/-- One terminal-rule candidate at one input position. -/
abbrev CYKTerminalCandidate
    (N : Type u)
    (n : Nat) :=
  N × Fin n

/-- Embed an input position as a left CYK boundary. -/
def cykLeftBoundary
    {n : Nat}
    (i : Fin n) :
    Fin (n + 1) :=
  ⟨i.1, Nat.lt_trans i.2 (Nat.lt_succ_self n)⟩

/-- The boundary immediately after an input position. -/
def cykRightBoundary
    {n : Nat}
    (i : Fin n) :
    Fin (n + 1) :=
  ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

@[simp] theorem cykLeftBoundary_val
    {n : Nat}
    (i : Fin n) :
    (cykLeftBoundary i).1 = i.1 :=
  rfl

@[simp] theorem cykRightBoundary_val
    {n : Nat}
    (i : Fin n) :
    (cykRightBoundary i).1 = i.1 + 1 :=
  rfl

/-- Chart entry created by a terminal candidate. -/
def cykTerminalOutput
    (w : Word α)
    (c : CYKTerminalCandidate N w.length) :
    CYKSpan N w.length :=
  (c.1,
    (cykLeftBoundary c.2,
      cykRightBoundary c.2))

/-- A terminal candidate is enabled exactly by the corresponding grammar rule. -/
def CYKTerminalEnabled
    (terminalRule : N → α → Prop)
    (w : Word α)
    (c : CYKTerminalCandidate N w.length) : Prop :=
  terminalRule c.1 (w.get c.2)


instance instDecidableCYKTerminalEnabled
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (w : Word α) :
    DecidablePred (CYKTerminalEnabled terminalRule w) :=
  fun c => by
    unfold CYKTerminalEnabled
    infer_instance

/-- Executable initial CYK chart. -/
def cykTerminalSeed
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (w : Word α) :
    CYKChart N w.length :=
  (Finset.univ.filter
      (CYKTerminalEnabled terminalRule w)).image
    (cykTerminalOutput w)

/-- Exact size of the finite terminal candidate scan. -/
theorem cykTerminalCandidate_card_eq
    [Fintype N]
    (n : Nat) :
    Fintype.card (CYKTerminalCandidate N n) =
      Fintype.card N * n := by
  simp [CYKTerminalCandidate]

/-- The initial chart cannot contain more entries than terminal candidates. -/
theorem cykTerminalSeed_card_le
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (w : Word α) :
    (cykTerminalSeed terminalRule w).card ≤
      Fintype.card N * w.length := by
  unfold cykTerminalSeed
  calc
    ((Finset.univ.filter
        (CYKTerminalEnabled terminalRule w)).image
          (cykTerminalOutput w)).card
      ≤
    (Finset.univ.filter
        (CYKTerminalEnabled terminalRule w)).card :=
      Finset.card_image_le
    _ ≤
    (Finset.univ :
      Finset (CYKTerminalCandidate N w.length)).card :=
      Finset.card_filter_le _ _
    _ =
    Fintype.card N * w.length := by
      rw [Finset.card_univ]
      exact cykTerminalCandidate_card_eq w.length

/-- Every terminal output is a unit-length span. -/
theorem cykTerminalOutput_unit_span
    (w : Word α)
    (c : CYKTerminalCandidate N w.length) :
    (cykTerminalOutput w c).2.2.1 =
      (cykTerminalOutput w c).2.1.1 + 1 := by
  rfl

/--
An enabled terminal candidate carries an ordinary one-letter derivation.
-/
theorem cykTerminalEnabled_derives
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (w : Word α)
    (c : CYKTerminalCandidate N w.length)
    (hen :
      CYKTerminalEnabled terminalRule w c) :
    UntypedDerives terminalRule binaryRule
      c.1 [w.get c.2] := by
  exact UntypedDerives.terminal hen

end BinaryMembershipSeed

end TCS1
end LeanCfgProject
