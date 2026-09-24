import LeanCfgProject.TCS1.YieldTypedRefinementCore
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# TCS #1 v79: binary-CFG membership kernel

This module starts the internal replacement for the last background
algorithmic fact used by the polynomial-update corollary: membership for the
terminal/binary SSBNF fragment is decidable in polynomial time by a CYK-style
dynamic program.

The current kernel establishes the two structural facts needed by that
algorithm:

* every terminal/binary derivation has parse-tree height at most its word
  length, so a bottom-up chart needs at most n rounds on an n-symbol input;
* the finite chart and binary-combination candidate spaces have the standard
  polynomial cardinalities |N|(n+1)^2 and |N|^3(n+1)^3.

A later layer turns these finite candidate spaces into the executable chart
closure and connects the resulting Boolean membership test back to
UntypedDerives.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryMembershipKernel

variable {N : Type u}
variable {α : Type v}

inductive UntypedDerivesHeight
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop) :
    N → Word α → Nat → Prop
  | terminal
      {A : N} {a : α}
      (hterm : terminalRule A a) :
      UntypedDerivesHeight terminalRule binaryRule A [a] 1
  | binary
      {A B C : N}
      {wB wC : Word α}
      {hB hC : Nat}
      (hbin : binaryRule A B C)
      (dB :
        UntypedDerivesHeight
          terminalRule binaryRule B wB hB)
      (dC :
        UntypedDerivesHeight
          terminalRule binaryRule C wC hC) :
      UntypedDerivesHeight
        terminalRule binaryRule
        A (wB ++ wC) (max hB hC + 1)

theorem untypedDerivesHeight_erase
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N} {w : Word α} {h : Nat}
    (d :
      UntypedDerivesHeight
        terminalRule binaryRule A w h) :
    UntypedDerives terminalRule binaryRule A w := by
  induction d with
  | terminal hterm =>
      exact UntypedDerives.terminal hterm
  | binary hbin _ _ ihB ihC =>
      exact UntypedDerives.binary hbin ihB ihC

theorem untypedDerives_exists_height
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N} {w : Word α}
    (d :
      UntypedDerives terminalRule binaryRule A w) :
    ∃ h : Nat,
      UntypedDerivesHeight
        terminalRule binaryRule A w h := by
  induction d with
  | terminal hterm =>
      exact ⟨1, UntypedDerivesHeight.terminal hterm⟩
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      rcases ihB with ⟨hB, dhB⟩
      rcases ihC with ⟨hC, dhC⟩
      exact
        ⟨max hB hC + 1,
          UntypedDerivesHeight.binary
            hbin dhB dhC⟩

theorem untypedDerivesHeight_length_pos
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N} {w : Word α} {h : Nat}
    (d :
      UntypedDerivesHeight
        terminalRule binaryRule A w h) :
    0 < w.length := by
  exact
    untypedDerives_length_pos
      terminalRule binaryRule
      (untypedDerivesHeight_erase
        terminalRule binaryRule d)

theorem untypedDerivesHeight_height_le_length
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N} {w : Word α} {h : Nat}
    (d :
      UntypedDerivesHeight
        terminalRule binaryRule A w h) :
    h ≤ w.length := by
  induction d with
  | terminal hterm =>
      simp
  | @binary A B C wB wC hB hC hbin dB dC ihB ihC =>
      have hBpos :
          0 < wB.length :=
        untypedDerivesHeight_length_pos
          terminalRule binaryRule dB
      have hCpos :
          0 < wC.length :=
        untypedDerivesHeight_length_pos
          terminalRule binaryRule dC
      simp only [List.length_append]
      have hmB : hB ≤ max hB hC :=
        Nat.le_max_left _ _
      have hmC : hC ≤ max hB hC :=
        Nat.le_max_right _ _
      omega

theorem untypedDerives_exists_height_le_length
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N} {w : Word α}
    (d :
      UntypedDerives terminalRule binaryRule A w) :
    ∃ h : Nat,
      UntypedDerivesHeight
          terminalRule binaryRule A w h
      ∧
      h ≤ w.length := by
  obtain ⟨h, dh⟩ :=
    untypedDerives_exists_height
      terminalRule binaryRule d
  exact
    ⟨h, dh,
      untypedDerivesHeight_height_le_length
        terminalRule binaryRule dh⟩

abbrev CYKSpan
    (N : Type u)
    (n : Nat) :=
  N × (Fin (n + 1) × Fin (n + 1))

abbrev CYKBinaryCandidate
    (N : Type u)
    (n : Nat) :=
  (N × N × N) ×
    (Fin (n + 1) × Fin (n + 1) × Fin (n + 1))

theorem cykSpan_card_eq
    [Fintype N]
    (n : Nat) :
    Fintype.card (CYKSpan N n) =
      Fintype.card N * (n + 1) ^ 2 := by
  simp [CYKSpan, pow_two]

theorem cykBinaryCandidate_card_eq
    [Fintype N]
    (n : Nat) :
    Fintype.card (CYKBinaryCandidate N n) =
      (Fintype.card N) ^ 3 * (n + 1) ^ 3 := by
  simp [CYKBinaryCandidate, pow_succ, Nat.mul_assoc]

def cykRoundScanEnvelope
    (nonterminalCount inputLength : Nat) : Nat :=
  inputLength *
    (nonterminalCount ^ 3 *
      (inputLength + 1) ^ 3)

theorem cykRoundScanEnvelope_eq
    (m n : Nat) :
    cykRoundScanEnvelope m n =
      m ^ 3 * n * (n + 1) ^ 3 := by
  unfold cykRoundScanEnvelope
  ring

theorem cyk_full_scan_count
    [Fintype N]
    (n : Nat) :
    n * Fintype.card (CYKBinaryCandidate N n)
      =
    cykRoundScanEnvelope
      (Fintype.card N) n := by
  rw [cykBinaryCandidate_card_eq]
  unfold cykRoundScanEnvelope
  ring

end BinaryMembershipKernel

end TCS1
end LeanCfgProject
