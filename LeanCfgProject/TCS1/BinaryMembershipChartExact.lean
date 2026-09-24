import LeanCfgProject.TCS1.BinaryMembershipChartComplete

/-!
# TCS #1 v79: exact executable CYK completeness

This module closes the semantic correctness loop for the executable finite
CYK chart.  The core induction embeds an exact-height derivation into an
arbitrary input slice.  Combined with chart soundness and the height bound from
BinaryMembershipKernel, the full-span chart after |w| rounds is equivalent to
ordinary terminal/binary derivability.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryMembershipChartExact

variable {N : Type u}
variable {α : Type v}

/--
An exact-height derivation of a slice appears in the executable chart after
that many cumulative binary rounds.
-/
theorem untypedDerivesHeight_chart_complete
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    {A : N}
    {x : Word α}
    {h : Nat}
    (d :
      UntypedDerivesHeight
        terminalRule binaryRule A x h) :
    ∀ (w : Word α)
      (i j : Fin (w.length + 1)),
      cykSlice w i j = x →
      (A, (i, j)) ∈
        cykChartIterate binaryRule
          (cykTerminalSeed terminalRule w) h := by
  induction d with
  | @terminal A a hterm =>
      intro w i j hslice
      have hslicePos :
          0 < (cykSlice w i j).length := by
        rw [hslice]
        simp
      have hspanPos :
          0 < j.1 - i.1 :=
        lt_of_lt_of_le hslicePos
          (cykSlice_length_le_span w i j)
      have hij : i.1 < j.1 :=
        Nat.sub_pos_iff_lt.mp hspanPos
      have hjw : j.1 ≤ w.length := by
        omega
      have hiw : i.1 < w.length := by
        omega
      let p : Fin w.length :=
        ⟨i.1, hiw⟩
      have hleft :
          cykLeftBoundary p = i := by
        apply Fin.ext
        rfl
      have hlen :=
        congrArg List.length hslice
      rw [cykSlice_length_eq_span
        w i j (Nat.le_of_lt hij)] at hlen
      have hji : j.1 = i.1 + 1 := by
        simp only [List.length_singleton] at hlen
        omega
      have hright :
          cykRightBoundary p = j := by
        apply Fin.ext
        exact hji.symm
      have hterminalSlice :=
        cykSlice_terminal w p
      rw [hleft, hright] at hterminalSlice
      have hsingleton :
          [w.get p] = [a] :=
        hterminalSlice.symm.trans hslice
      have hget : w.get p = a := by
        simpa using hsingleton
      have hterm' :
          terminalRule A (w.get p) := by
        rw [hget]
        exact hterm
      have hseed :
          (A,
            (cykLeftBoundary p,
              cykRightBoundary p))
            ∈ cykTerminalSeed terminalRule w :=
        cykTerminalSeed_complete
          terminalRule w A p hterm'
      rw [hleft, hright] at hseed
      exact
        cykChartIterate_mono_succ
          binaryRule
          (cykTerminalSeed terminalRule w)
          0 hseed

  | @binary A B C wB wC hB hC hbin dB dC ihB ihC =>
      intro w i j hslice
      have hBpos : 0 < wB.length :=
        untypedDerivesHeight_length_pos
          terminalRule binaryRule dB
      have hCpos : 0 < wC.length :=
        untypedDerivesHeight_length_pos
          terminalRule binaryRule dC
      have hslicePos :
          0 < (cykSlice w i j).length := by
        rw [hslice, List.length_append]
        omega
      have hspanPos :
          0 < j.1 - i.1 :=
        lt_of_lt_of_le hslicePos
          (cykSlice_length_le_span w i j)
      have hij : i.1 < j.1 :=
        Nat.sub_pos_iff_lt.mp hspanPos
      have hlen0 :=
        congrArg List.length hslice
      rw [cykSlice_length_eq_span
        w i j (Nat.le_of_lt hij)] at hlen0
      have hlen :
          j.1 - i.1 =
            wB.length + wC.length := by
        simpa [List.length_append] using hlen0

      let kval : Nat := i.1 + wB.length
      have hjw : j.1 ≤ w.length := by
        omega
      have hikVal : i.1 < kval := by
        dsimp [kval]
        omega
      have hkjVal : kval < j.1 := by
        dsimp [kval]
        omega
      have hkw : kval ≤ w.length := by
        omega
      let k : Fin (w.length + 1) :=
        ⟨kval, Nat.lt_succ_of_le hkw⟩
      have hik : i.1 < k.1 := by
        simpa [k] using hikVal
      have hkj : k.1 < j.1 := by
        simpa [k] using hkjVal

      have hsplit :=
        cykSlice_split w i k j
          (Nat.le_of_lt hik)
          (Nat.le_of_lt hkj)
      have hcat :
          cykSlice w i k ++
              cykSlice w k j
            =
          wB ++ wC := by
        rw [← hsplit]
        exact hslice

      have hleftLen :
          (cykSlice w i k).length =
            wB.length := by
        rw [cykSlice_length_eq_span
          w i k (Nat.le_of_lt hik)]
        change kval - i.1 = wB.length
        dsimp [kval]
        omega

      have htake :=
        congrArg (List.take wB.length) hcat
      have hleftEq :
          cykSlice w i k = wB := by
        simpa [hleftLen] using htake
      have hrightEq :
          cykSlice w k j = wC := by
        rw [hleftEq] at hcat
        exact List.append_cancel_left hcat

      have memB :=
        ihB w i k hleftEq
      have memC :=
        ihC w k j hrightEq
      let m := max hB hC
      have memBm :
          (B, (i, k)) ∈
            cykChartIterate binaryRule
              (cykTerminalSeed terminalRule w) m :=
        cykChartIterate_mono
          binaryRule
          (cykTerminalSeed terminalRule w)
          (Nat.le_max_left hB hC)
          memB
      have memCm :
          (C, (k, j)) ∈
            cykChartIterate binaryRule
              (cykTerminalSeed terminalRule w) m :=
        cykChartIterate_mono
          binaryRule
          (cykTerminalSeed terminalRule w)
          (Nat.le_max_right hB hC)
          memC
      have hparent :=
        cykChartStep_complete_binary
          binaryRule
          (cykChartIterate binaryRule
            (cykTerminalSeed terminalRule w) m)
          A B C i k j hik hkj hbin
          memBm memCm
      simpa [m, cykChartIterate] using hparent

/-- Left boundary of the full input span. -/
def cykFullLeft
    (w : Word α) :
    Fin (w.length + 1) :=
  ⟨0, Nat.succ_pos _⟩

/-- Right boundary of the full input span. -/
def cykFullRight
    (w : Word α) :
    Fin (w.length + 1) :=
  ⟨w.length, Nat.lt_succ_self _⟩

@[simp] theorem cykFullLeft_val
    (w : Word α) :
    (cykFullLeft w).1 = 0 :=
  rfl

@[simp] theorem cykFullRight_val
    (w : Word α) :
    (cykFullRight w).1 = w.length :=
  rfl

/-- The full CYK input span is exactly the input word. -/
theorem cykSlice_full
    (w : Word α) :
    cykSlice w
        (cykFullLeft w)
        (cykFullRight w)
      =
    w := by
  unfold cykSlice cykFullLeft cykFullRight
  simp

/-- Ordinary derivability implies membership in the saturated full-span chart. -/
theorem cykFullSpan_complete
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    (A : N)
    (w : Word α)
    (d :
      UntypedDerives terminalRule binaryRule A w) :
    (A,
      (cykFullLeft w,
        cykFullRight w))
      ∈
    cykChartIterate binaryRule
      (cykTerminalSeed terminalRule w)
      w.length := by
  obtain ⟨h, dh, hle⟩ :=
    untypedDerives_exists_height_le_length
      terminalRule binaryRule d
  have hm :
      (A,
        (cykFullLeft w,
          cykFullRight w))
        ∈
      cykChartIterate binaryRule
        (cykTerminalSeed terminalRule w) h :=
    untypedDerivesHeight_chart_complete
      terminalRule binaryRule dh
      w (cykFullLeft w) (cykFullRight w)
      (cykSlice_full w)
  exact
    cykChartIterate_mono
      binaryRule
      (cykTerminalSeed terminalRule w)
      hle hm

/-- Full-span chart membership is semantically sound. -/
theorem cykFullSpan_sound
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    (A : N)
    (w : Word α)
    (hmem :
      (A,
        (cykFullLeft w,
          cykFullRight w))
        ∈
      cykChartIterate binaryRule
        (cykTerminalSeed terminalRule w)
        w.length) :
    UntypedDerives terminalRule binaryRule A w := by
  have hsound :=
    cykChartIterate_sound
      terminalRule binaryRule w w.length
  have d :=
    hsound
      (A, (cykFullLeft w, cykFullRight w))
      hmem
  simpa [cykSlice_full] using d

/-- Exact correctness theorem for the executable full-span CYK chart. -/
theorem cykFullSpan_iff_derives
    [Fintype N]
    [DecidableEq N]
    (terminalRule : N → α → Prop)
    [DecidableRel terminalRule]
    (binaryRule : N → N → N → Prop)
    [∀ A B : N, DecidablePred (binaryRule A B)]
    (A : N)
    (w : Word α) :
    (A,
      (cykFullLeft w,
        cykFullRight w))
      ∈
    cykChartIterate binaryRule
      (cykTerminalSeed terminalRule w)
      w.length
      ↔
    UntypedDerives terminalRule binaryRule A w := by
  constructor
  · exact
      cykFullSpan_sound
        terminalRule binaryRule A w
  · exact
      cykFullSpan_complete
        terminalRule binaryRule A w

end BinaryMembershipChartExact

end TCS1
end LeanCfgProject
