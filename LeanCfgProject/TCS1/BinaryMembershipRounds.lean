import LeanCfgProject.TCS1.BinaryMembershipKernel

/-!
# TCS #1 v79: exact bounded CYK-round semantics

This module supplies the semantic half of the internal membership algorithm.
CYKRound r A w means that the terminal/binary grammar can derive w from A
using a parse tree of height at most r.

The key endpoint is exact:

  CYKRound |w| A w  <->  UntypedDerives A w.

Thus the input length is a sufficient finite saturation bound. The previous
module already bounds the complete finite span/candidate spaces scanned at
each round.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryMembershipRounds

variable {N : Type u}
variable {α : Type v}

inductive CYKRound
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop) :
    Nat → N → Word α → Prop
  | terminal
      {A : N} {a : α}
      (hterm : terminalRule A a) :
      CYKRound terminalRule binaryRule 1 A [a]
  | carry
      {r : Nat} {A : N} {w : Word α}
      (d : CYKRound terminalRule binaryRule r A w) :
      CYKRound terminalRule binaryRule (r + 1) A w
  | binary
      {r : Nat}
      {A B C : N}
      {wB wC : Word α}
      (hbin : binaryRule A B C)
      (dB : CYKRound terminalRule binaryRule r B wB)
      (dC : CYKRound terminalRule binaryRule r C wC) :
      CYKRound terminalRule binaryRule
        (r + 1) A (wB ++ wC)

theorem cykRound_erase
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {r : Nat} {A : N} {w : Word α}
    (d : CYKRound terminalRule binaryRule r A w) :
    UntypedDerives terminalRule binaryRule A w := by
  induction d with
  | terminal hterm =>
      exact UntypedDerives.terminal hterm
  | carry _ ih =>
      exact ih
  | binary hbin _ _ ihB ihC =>
      exact UntypedDerives.binary hbin ihB ihC

theorem cykRound_mono
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {r s : Nat} {A : N} {w : Word α}
    (hrs : r ≤ s)
    (d : CYKRound terminalRule binaryRule r A w) :
    CYKRound terminalRule binaryRule s A w := by
  induction s, hrs using Nat.le_induction with
  | base =>
      exact d
  | succ s hrs ih =>
      exact CYKRound.carry ih

theorem cykRound_of_exact_height
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N} {w : Word α} {h : Nat}
    (d :
      UntypedDerivesHeight
        terminalRule binaryRule A w h) :
    CYKRound terminalRule binaryRule h A w := by
  induction d with
  | terminal hterm =>
      exact CYKRound.terminal hterm
  | @binary A B C wB wC hB hC hbin dB dC ihB ihC =>
      let m := max hB hC
      have hB_le : hB ≤ m :=
        Nat.le_max_left _ _
      have hC_le : hC ≤ m :=
        Nat.le_max_right _ _
      have dB' :
          CYKRound terminalRule binaryRule m B wB :=
        cykRound_mono
          terminalRule binaryRule hB_le ihB
      have dC' :
          CYKRound terminalRule binaryRule m C wC :=
        cykRound_mono
          terminalRule binaryRule hC_le ihC
      exact CYKRound.binary hbin dB' dC'

theorem cykRound_of_height
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N} {w : Word α} {h r : Nat}
    (d :
      UntypedDerivesHeight
        terminalRule binaryRule A w h)
    (hhr : h ≤ r) :
    CYKRound terminalRule binaryRule r A w := by
  exact
    cykRound_mono
      terminalRule binaryRule hhr
      (cykRound_of_exact_height
        terminalRule binaryRule d)

theorem cykRound_complete_at_length
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N} {w : Word α}
    (d :
      UntypedDerives terminalRule binaryRule A w) :
    CYKRound terminalRule binaryRule
      w.length A w := by
  obtain ⟨h, dh, hh⟩ :=
    untypedDerives_exists_height_le_length
      terminalRule binaryRule d
  exact
    cykRound_of_height
      terminalRule binaryRule dh hh

theorem cykRound_length_iff_derives
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (A : N)
    (w : Word α) :
    CYKRound terminalRule binaryRule
        w.length A w
      ↔
    UntypedDerives terminalRule binaryRule A w := by
  constructor
  · exact
      cykRound_erase terminalRule binaryRule
  · exact
      cykRound_complete_at_length
        terminalRule binaryRule

theorem not_cykRound_zero
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (A : N)
    (w : Word α) :
    ¬ CYKRound terminalRule binaryRule 0 A w := by
  intro d
  cases d

end BinaryMembershipRounds

end TCS1
end LeanCfgProject
