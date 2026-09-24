import LeanCfgProject.TCS1.PreparedLinearNormalizationFacade
import LeanCfgProject.TCS1.TerminalIsolationKernel
import Mathlib.Tactic

/-!
# TCS #1: decomposition of linear mixed right-hand sides

This module connects the ordinary mixed-symbol representation of a finite CFG
to the prepared linear right-hand sides consumed by the verified specialized
binarization.

A mixed RHS is called linear when it contains at most one nonterminal.
Such an RHS is either a terminal word or uniquely has the form u B v with
terminal words u and v. After the standard preprocessing has removed empty
and unit non-start rules, every linear RHS therefore has a prepared linear
representation.

We also prove exact RHS semantics and length preservation for the translation.
These are the local facts needed to connect epsilon/unit preprocessing to the
concrete linear-spine normalization.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section LinearMixedRhsDecomposition

variable {N : Type u}
variable {α : Type v}

/-- Number of nonterminal occurrences in a mixed right-hand side. -/
def mixedRhsNonterminalCount :
    List (MixedSymbol N α) → Nat
  | [] => 0
  | Sum.inl _ :: rest =>
      mixedRhsNonterminalCount rest + 1
  | Sum.inr _ :: rest =>
      mixedRhsNonterminalCount rest


/-- A list of literal terminals contains no nonterminal occurrences. -/
@[simp] theorem mixedRhsNonterminalCount_map_terminal
    (xs : List α) :
    mixedRhsNonterminalCount
      (xs.map (fun a => (Sum.inr a : MixedSymbol N α))) = 0 := by
  induction xs with
  | nil =>
      rfl
  | cons a rest ih =>
      simpa [mixedRhsNonterminalCount] using ih

/-- A literal terminal prefix does not change the nonterminal count. -/
@[simp] theorem mixedRhsNonterminalCount_terminalPrefix
    (xs : List α)
    (rhs : List (MixedSymbol N α)) :
    mixedRhsNonterminalCount
      (xs.map (fun a => (Sum.inr a : MixedSymbol N α)) ++ rhs)
      =
    mixedRhsNonterminalCount rhs := by
  induction xs with
  | nil =>
      rfl
  | cons a rest ih =>
      simpa [mixedRhsNonterminalCount] using ih

/-- A mixed RHS is linear iff it contains at most one nonterminal. -/
def MixedRhsLinear
    (rhs : List (MixedSymbol N α)) : Prop :=
  mixedRhsNonterminalCount rhs ≤ 1

/-- Zero nonterminal count means that the RHS is literally a terminal list. -/
theorem mixedRhsNonterminalCount_eq_zero_iff
    (rhs : List (MixedSymbol N α)) :
    mixedRhsNonterminalCount rhs = 0
      ↔
    ∃ xs : List α,
      rhs = xs.map Sum.inr := by
  induction rhs with
  | nil =>
      exact ⟨fun _ => ⟨[], rfl⟩, fun _ => rfl⟩
  | cons s rest ih =>
      cases s with
      | inl A =>
          constructor
          · intro h
            simp [mixedRhsNonterminalCount] at h
          · rintro ⟨xs, hxs⟩
            cases xs with
            | nil =>
                simp at hxs
            | cons a tail =>
                simp at hxs
      | inr a =>
          constructor
          · intro h
            have hrest :
                mixedRhsNonterminalCount rest = 0 := by
              simpa [mixedRhsNonterminalCount] using h
            obtain ⟨xs, rfl⟩ := ih.mp hrest
            exact ⟨a :: xs, by simp⟩
          · rintro ⟨xs, hxs⟩
            cases xs with
            | nil =>
                simp at hxs
            | cons b tail =>
                have hEq :
                    a = b ∧
                    rest =
                      tail.map
                        (fun x =>
                          (Sum.inr x : MixedSymbol N α)) := by
                  simpa using hxs
                rcases hEq with ⟨rfl, rfl⟩
                simp [mixedRhsNonterminalCount]

/--
Every linear mixed RHS is either terminal-only or has exactly one
nonterminal, surrounded by terminal words.
-/
theorem mixedRhsLinear_decomposition
    (rhs : List (MixedSymbol N α))
    (hlin : MixedRhsLinear rhs) :
    (∃ xs : List α,
        rhs = xs.map Sum.inr)
      ∨
    (∃ left : List α, ∃ B : N, ∃ right : List α,
        rhs =
          left.map Sum.inr ++
            [Sum.inl B] ++
            right.map Sum.inr) := by
  induction rhs with
  | nil =>
      exact Or.inl ⟨[], rfl⟩
  | cons s rest ih =>
      cases s with
      | inr a =>
          have hrest : MixedRhsLinear rest := by
            exact hlin
          rcases ih hrest with hterm | haround
          · rcases hterm with ⟨xs, rfl⟩
            exact Or.inl ⟨a :: xs, by simp⟩
          · rcases haround with
              ⟨left, B, right, hEq⟩
            subst rest
            exact Or.inr
              ⟨a :: left, B, right, by simp⟩
      | inl B =>
          have hzero :
              mixedRhsNonterminalCount rest = 0 := by
            unfold MixedRhsLinear at hlin
            simp only [mixedRhsNonterminalCount] at hlin
            omega
          obtain ⟨right, hright⟩ :=
            (mixedRhsNonterminalCount_eq_zero_iff rest).1 hzero
          subst rest
          exact Or.inr
            ⟨[], B, right, by simp⟩

/-- Mixed RHS represented by a prepared linear RHS. -/
def PreparedLinearRhs.toMixedRhs :
    PreparedLinearRhs N α →
      List (MixedSymbol N α)
  | .terminals head tail =>
      (head :: tail).map Sum.inr
  | .around left core right _ =>
      left.map Sum.inr ++
        [Sum.inl core] ++
        right.map Sum.inr

/-- Prepared conversion preserves the exact mixed-symbol length. -/
@[simp] theorem PreparedLinearRhs.toMixedRhs_length
    (rhs : PreparedLinearRhs N α) :
    rhs.toMixedRhs.length =
      rhs.sourceLength := by
  cases rhs with
  | terminals head tail =>
      simp [PreparedLinearRhs.toMixedRhs,
        PreparedLinearRhs.sourceLength]
  | around left core right hnonunit =>
      simp [PreparedLinearRhs.toMixedRhs,
        PreparedLinearRhs.sourceLength]
      omega

/--
A terminal prefix on an ordinary mixed RHS realizes exactly that prefix
followed by a realization of the remaining suffix.
-/
theorem rhsRealizes_terminalPrefix_iff
    (L : N → Set (List α))
    (stem : List α)
    (rhs : List (MixedSymbol N α))
    (word : List α) :
    RhsRealizes L
        (stem.map Sum.inr ++ rhs) word
      ↔
    ∃ tail,
      word = stem ++ tail ∧
      RhsRealizes L rhs tail := by
  induction stem generalizing word with
  | nil =>
      simp
  | cons a rest ih =>
      simp only [List.map_cons, List.cons_append]
      constructor
      · intro h
        rcases h with ⟨tail, hword, htail⟩
        have hsuffix :=
          (ih tail).1 htail
        rcases hsuffix with
          ⟨suffix, htailEq, hsuffix⟩
        refine ⟨suffix, ?_, hsuffix⟩
        rw [hword, htailEq]
      · rintro ⟨suffix, hword, hsuffix⟩
        refine ⟨rest ++ suffix, ?_, ?_⟩
        · rw [hword]
        · exact
            (ih (rest ++ suffix)).2
              ⟨suffix, rfl, hsuffix⟩

/-- A terminal-only mixed RHS realizes exactly its literal terminal word. -/
theorem rhsRealizes_terminalWord_iff
    (L : N → Set (List α))
    (xs word : List α) :
    RhsRealizes L (xs.map Sum.inr) word
      ↔
    word = xs := by
  have h :=
    rhsRealizes_terminalPrefix_iff
      L xs [] word
  constructor
  · intro hw
    rcases h.mp (by simpa using hw) with
      ⟨tail, hword, htail⟩
    have hnil : tail = [] := htail
    subst tail
    simpa using hword
  · intro hword
    subst word
    simpa using
      h.mpr ⟨[], by simp, rfl⟩

/--
The prepared representation and the ordinary mixed RHS have exactly the same
one-step terminal-word semantics under every nonterminal interpretation.
-/
theorem preparedLinearRhs_realizes_iff_mixed
    (L : N → Set (List α))
    (rhs : PreparedLinearRhs N α)
    (word : List α) :
    PreparedLinearRhs.realizes L rhs word
      ↔
    RhsRealizes L rhs.toMixedRhs word := by
  cases rhs with
  | terminals head tail =>
      change
        word = head :: tail
          ↔
        RhsRealizes L
          ((head :: tail).map Sum.inr) word
      exact
        (rhsRealizes_terminalWord_iff
          L (head :: tail) word).symm
  | around left core right hnonunit =>
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hp :
            RhsRealizes L
              (left.map Sum.inr ++
                ([Sum.inl core] ++ right.map Sum.inr))
              (left ++ z ++ right) := by
          apply
            (rhsRealizes_terminalPrefix_iff
              L left
              ([Sum.inl core] ++
                right.map Sum.inr)
              (left ++ z ++ right)).2
          refine ⟨z ++ right, by simp, ?_⟩
          refine ⟨z, right, rfl, hz, ?_⟩
          exact
            (rhsRealizes_terminalWord_iff
              L right right).2 rfl
        simpa [PreparedLinearRhs.toMixedRhs,
          List.append_assoc] using hp
      · intro h
        have h' :
            RhsRealizes L
              (left.map Sum.inr ++
                ([Sum.inl core] ++ right.map Sum.inr))
              word := by
          simpa [PreparedLinearRhs.toMixedRhs,
            List.append_assoc] using h
        have hp :=
          (rhsRealizes_terminalPrefix_iff
            L left
            ([Sum.inl core] ++
              right.map Sum.inr)
            word).1 h'
        rcases hp with ⟨tail, hword, htail⟩
        rcases htail with
          ⟨z, suffix, htailEq, hz, hsuffix⟩
        have hsuffixEq :
            suffix = right :=
          (rhsRealizes_terminalWord_iff
            L right suffix).1 hsuffix
        subst suffix
        subst tail
        exact ⟨z, hz,
          by simpa [List.append_assoc] using hword⟩

/--
After empty and unit rules have been removed, every linear mixed RHS has a
prepared representation.
-/
theorem exists_preparedLinearRhs_of_linear_nonempty_nonunit
    (rhs : List (MixedSymbol N α))
    (hlin : MixedRhsLinear rhs)
    (hnonempty : rhs ≠ [])
    (hnonunit :
      ∀ B : N, rhs ≠ [Sum.inl B]) :
    ∃ prepared : PreparedLinearRhs N α,
      prepared.toMixedRhs = rhs := by
  rcases mixedRhsLinear_decomposition rhs hlin with
    hterm | haround
  · rcases hterm with ⟨xs, hEq⟩
    cases xs with
    | nil =>
        simp at hEq
        exact False.elim (hnonempty hEq)
    | cons head tail =>
        refine
          ⟨PreparedLinearRhs.terminals head tail, ?_⟩
        simpa [PreparedLinearRhs.toMixedRhs] using hEq.symm
  · rcases haround with
      ⟨left, B, right, hEq⟩
    have hnonunitContext :
        left ≠ [] ∨ right ≠ [] := by
      by_cases hleft : left = []
      · right
        intro hright
        subst left
        subst right
        have hunit :
            rhs = [Sum.inl B] := by
          simpa using hEq
        exact (hnonunit B) hunit
      · exact Or.inl hleft
    refine
      ⟨PreparedLinearRhs.around
        left B right hnonunitContext, ?_⟩
    simpa [PreparedLinearRhs.toMixedRhs] using hEq.symm

/-- Every prepared mixed RHS is itself linear. -/
theorem PreparedLinearRhs.toMixedRhs_linear
    (rhs : PreparedLinearRhs N α) :
    MixedRhsLinear rhs.toMixedRhs := by
  unfold MixedRhsLinear
  cases rhs with
  | terminals head tail =>
      simp [PreparedLinearRhs.toMixedRhs,
        mixedRhsNonterminalCount]
  | around left core right hnonunit =>
      simp [PreparedLinearRhs.toMixedRhs,
        mixedRhsNonterminalCount]

end LinearMixedRhsDecomposition

end TCS1
end LeanCfgProject
