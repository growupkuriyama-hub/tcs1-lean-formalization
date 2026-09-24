import LeanCfgProject.TCS1.BinarizationKernel

/-!
# TCS #1 v65: front-end thickness preservation

This module formalizes the quantitative statement in Appendix A that
terminal isolation and binarization preserve short terminal witnesses up to
a linear factor in the original grammar size.

Old nonterminals keep their original terminal language, while every fresh
terminal wrapper W_a derives the one-letter word [a]. Hence, if every old
productive nonterminal has a witness of length at most tau_R, every isolated
state has one of length at most tau_R+1. A fresh binarization suffix spanning
at most n isolated states then has a witness of length at most
n*(tau_R+1).
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FrontEndThickness

variable {N : Type u}
variable {α : Type v}

/--
Terminal isolation raises the uniform old-state witness bound from tau_R to
the harmless positive envelope tau_R+1, covering wrappers as well.
-/
theorem isolatedInterpretation_short_witness
    (L : N → Set (List α))
    (τR : Nat)
    (hshort : ∀ A, ∃ w, w ∈ L A ∧ w.length ≤ τR) :
    ∀ X : N ⊕ α,
      ∃ w,
        w ∈ isolatedInterpretation L X ∧
        w.length ≤ thicknessBar τR := by
  intro X
  cases X with
  | inl A =>
      obtain ⟨w, hw, hlen⟩ := hshort A
      refine ⟨w, hw, ?_⟩
      unfold thicknessBar
      omega
  | inr a =>
      refine ⟨[a], ?_, ?_⟩
      · simp [isolatedInterpretation]
      · simp [thicknessBar]

/-- States occurring after the front-end terminal-isolation/binarization stage. -/
abbrev FrontEndState (N : Type u) (α : Type v) :=
  BinarizedState (N ⊕ α)

/--
Only suffix states whose represented contiguous block has length at most n
are admitted as front-end states created from an input of encoding size n.
-/
def FrontEndActive
    (n : Nat) :
    FrontEndState N α → Prop
  | BinarizedState.old _ => True
  | BinarizedState.suffix xs => xs.length ≤ n

/-- Semantic interpretation of the terminal-isolated, binarized front end. -/
def frontEndInterpretation
    (L : N → Set (List α)) :
    FrontEndState N α → Set (List α) :=
  binarizedInterpretation (isolatedInterpretation L)

/--
Every active front-end state has a terminal witness of length at most
n*(tau_R+1), provided n is positive.
-/
theorem frontEnd_active_short_witness
    (L : N → Set (List α))
    (n τR : Nat)
    (hn : 0 < n)
    (hshort : ∀ A, ∃ w, w ∈ L A ∧ w.length ≤ τR) :
    ∀ X : FrontEndState N α,
      FrontEndActive (N := N) (α := α) n X →
      ∃ w,
        w ∈ frontEndInterpretation L X ∧
        w.length ≤ n * thicknessBar τR := by
  intro X hactive
  cases X with
  | old Y =>
      obtain ⟨w, hw, hlen⟩ :=
        isolatedInterpretation_short_witness L τR hshort Y
      refine ⟨w, hw, ?_⟩
      have hOne : 1 ≤ n := hn
      have hmul :
          1 * thicknessBar τR ≤ n * thicknessBar τR :=
        Nat.mul_le_mul_right (thicknessBar τR) hOne
      have hbar :
          thicknessBar τR ≤ n * thicknessBar τR := by
        simpa using hmul
      exact le_trans hlen hbar
  | suffix xs =>
      exact suffix_short_witness_of_length_le
        (isolatedInterpretation L)
        (thicknessBar τR)
        n
        (isolatedInterpretation_short_witness L τR hshort)
        xs
        hactive

/--
Paper-facing c1=1 specialization for the explicit front-end model used here.
The manuscript allows an arbitrary fixed encoding constant c1; this theorem
checks the stronger symbol-count formulation n*(tau_R+1).
-/
theorem frontEnd_active_short_witness_binarizedEnvelope
    (L : N → Set (List α))
    (n τR : Nat)
    (hn : 0 < n)
    (hshort : ∀ A, ∃ w, w ∈ L A ∧ w.length ≤ τR)
    (X : FrontEndState N α)
    (hactive : FrontEndActive (N := N) (α := α) n X) :
    ∃ w,
      w ∈ frontEndInterpretation L X ∧
      w.length ≤ binarizedThicknessEnvelope 1 n τR := by
  obtain ⟨w, hw, hlen⟩ :=
    frontEnd_active_short_witness L n τR hn hshort X hactive
  refine ⟨w, hw, ?_⟩
  simpa [binarizedThicknessEnvelope] using hlen

end FrontEndThickness

end TCS1
end LeanCfgProject
