import LeanCfgProject.TCS1.LeastClosedCFGLanguage
import LeanCfgProject.TCS1.BinarizationLeastClosed

/-!
# TCS #1 v65: terminal-isolation / binarization bridge

After terminal isolation, every right-hand side is either a singleton terminal
or a sequence of nonterminals. This module converts the isolated mixed grammar
to the SequenceGrammar interface used by the binarization proof and proves
that the conversion preserves the least generated languages exactly.

Combining this bridge with terminalIsolation_leastClosedLanguage_eq and
binarization_leastLanguage_eq gives one theorem for the entire front end of
Appendix A: terminal isolation followed by binarization preserves the generated
language of every original nonterminal.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section TerminalIsolationBinarizationBridge

variable {N : Type u}
variable {α : Type v}

/-- Under full wrapping, a source symbol becomes the corresponding isolated state. -/
@[simp] theorem isolateSymbol_true_eq_inl
    (s : MixedSymbol N α) :
    isolateSymbol (N := N) (α := α) true s = Sum.inl s := by
  cases s <;> rfl

/-- Pointwise wrapping commutes with mapping over a whole mixed RHS. -/
@[simp] theorem map_isolateSymbol_true_eq_map_inl
    (xs : List (MixedSymbol N α)) :
    xs.map (isolateSymbol (N := N) (α := α) true) =
      xs.map Sum.inl := by
  induction xs with
  | nil =>
      rfl
  | cons s rest ih =>
      simp [ih]

/--
A right-hand side consisting only of nonterminal symbols realizes exactly the
same words as the corresponding NTSequenceRealizes sequence.
-/
theorem rhsRealizes_map_nonterminals_iff
    {X : Type u}
    (L : X → Set (List α))
    (xs : List X)
    (w : List α) :
    RhsRealizes L (xs.map Sum.inl) w ↔
      NTSequenceRealizes L xs w := by
  induction xs generalizing w with
  | nil =>
      simp [RhsRealizes, NTSequenceRealizes]
  | cons A rest ih =>
      simp [RhsRealizes, NTSequenceRealizes, ih]

/--
Sequence-grammar presentation of a terminal-isolated mixed grammar.
-/
def isolatedSequenceGrammar
    (R : MixedRules N α) :
    SequenceGrammar (N ⊕ α) α where
  terminal X a :=
    IsolatedRule R X [Sum.inr a]
  structural X xs :=
    IsolatedRule R X (xs.map Sum.inl)

/--
For every interpretation, one rule step of the isolated mixed grammar equals
one rule step of its sequence presentation.
-/
theorem isolated_ruleStep_eq_sequence
    (R : MixedRules N α)
    (L : (N ⊕ α) → Set (List α))
    (X : N ⊕ α) :
    RuleStepLanguage (IsolatedRule R) L X
      =
    SequenceRuleStepLanguage
      (isolatedSequenceGrammar R) L X := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    rcases hw with ⟨rhsIso, hrule, hreal⟩
    cases hrule with
    | wrapper a =>
        left
        refine ⟨a, IsolatedRule.wrapper a, ?_⟩
        simpa [RhsRealizes] using hreal
    | @original A rhs hR =>
        cases rhs with
        | nil =>
            right
            refine ⟨[], ?_, ?_⟩
            · simpa [isolatedSequenceGrammar, isolateRhs] using
                (IsolatedRule.original hR)
            · exact
                (rhsRealizes_map_nonterminals_iff
                  L [] w).1
                  (by simpa [isolateRhs] using hreal)
        | cons s rest =>
            cases rest with
            | nil =>
                cases s with
                | inr a =>
                    left
                    refine ⟨a, ?_, ?_⟩
                    · simpa [isolatedSequenceGrammar, isolateRhs] using
                        (IsolatedRule.original hR)
                    · simpa [RhsRealizes, isolateRhs] using hreal
                | inl B =>
                    right
                    refine ⟨[Sum.inl B], ?_, ?_⟩
                    · simpa [isolatedSequenceGrammar, isolateRhs,
                        isolateSymbol_true_eq_inl] using
                        (IsolatedRule.original hR)
                    · exact
                        (rhsRealizes_map_nonterminals_iff
                          L [Sum.inl B] w).1
                          (by
                            simpa [isolateRhs,
                              map_isolateSymbol_true_eq_map_inl] using hreal)
            | cons s₂ tail =>
                right
                refine ⟨s :: s₂ :: tail, ?_, ?_⟩
                · simpa [isolatedSequenceGrammar, isolateRhs,
                    map_isolateSymbol_true_eq_map_inl] using
                    (IsolatedRule.original hR)
                · exact
                    (rhsRealizes_map_nonterminals_iff
                      L (s :: s₂ :: tail) w).1
                      (by
                        simpa [isolateRhs,
                          map_isolateSymbol_true_eq_map_inl] using hreal)
  · intro hw
    rcases hw with hterm | hstruct
    · rcases hterm with ⟨a, hrule, rfl⟩
      exact
        ⟨[Sum.inr a], hrule,
          ⟨[], rfl, rfl⟩⟩
    · rcases hstruct with ⟨xs, hrule, hreal⟩
      exact
        ⟨xs.map Sum.inl, hrule,
          (rhsRealizes_map_nonterminals_iff
            L xs w).2 hreal⟩

/-- Mixed-rule closure and sequence-rule closure are the same predicate. -/
theorem isolated_closed_iff_sequence_closed
    (R : MixedRules N α)
    (L : (N ⊕ α) → Set (List α)) :
    GrammarClosed (IsolatedRule R) L ↔
      SequenceGrammarClosed
        (isolatedSequenceGrammar R) L := by
  constructor
  · intro hmixed X w hw
    apply hmixed X
    have heq := isolated_ruleStep_eq_sequence R L X
    rw [heq]
    exact hw
  · intro hseq X w hw
    apply hseq X
    have heq := isolated_ruleStep_eq_sequence R L X
    rw [← heq]
    exact hw

/--
The mixed and sequence presentations of the terminal-isolated grammar have
identical least generated languages.
-/
theorem isolated_leastLanguage_eq_sequenceLeast
    (R : MixedRules N α)
    (X : N ⊕ α) :
    SequenceLeastLanguage
        (isolatedSequenceGrammar R) X
      =
    LeastClosedLanguage (IsolatedRule R) X := by
  apply Set.ext
  intro w
  constructor
  · intro hseq L hmixed
    exact hseq L
      ((isolated_closed_iff_sequence_closed R L).1 hmixed)
  · intro hmixed L hseq
    exact hmixed L
      ((isolated_closed_iff_sequence_closed R L).2 hseq)

/--
Front-end semantic theorem for Appendix A.

Terminal isolation followed by binarization preserves the full generated
language of every original nonterminal.
-/
theorem terminalIsolation_then_binarization_language_eq
    (R : MixedRules N α)
    (A : N) :
    SequenceLeastLanguage
        (binarizedSequenceGrammar
          (isolatedSequenceGrammar R))
        (BinarizedState.old (Sum.inl A))
      =
    LeastClosedLanguage R A := by
  calc
    SequenceLeastLanguage
        (binarizedSequenceGrammar
          (isolatedSequenceGrammar R))
        (BinarizedState.old (Sum.inl A))
      =
    SequenceLeastLanguage
        (isolatedSequenceGrammar R)
        (Sum.inl A) :=
      binarization_leastLanguage_eq
        (isolatedSequenceGrammar R) (Sum.inl A)
    _ =
    LeastClosedLanguage
        (IsolatedRule R)
        (Sum.inl A) :=
      isolated_leastLanguage_eq_sequenceLeast R (Sum.inl A)
    _ =
    LeastClosedLanguage R A :=
      terminalIsolation_leastClosedLanguage_eq R A

end TerminalIsolationBinarizationBridge

end TCS1
end LeanCfgProject
