import LeanCfgProject.TCS1.ReconstructionSoundness
import LeanCfgProject.TCS1.NormalizationLanguageBounds

/-!
# TCS #1: semantic correctness of binary-first non-start epsilon elimination

This module formalizes the standard transformation used in the appendix after
terminal isolation and binarization.

The input grammar has terminal, binary, epsilon, and unit rules.  Epsilon
elimination keeps terminal/binary/unit rules and, from a binary rule A -> B C,

* adds A -> C when B is nullable;
* adds A -> B when C is nullable.

There are no longer right-hand sides, so these are the only deletion variants.
We prove exact preservation of every nonempty terminal language:

  A =>*_G w  iff  A =>*_{eps-free} w        for w != epsilon.

This supplies the semantic fact invoked in the normalization proof rather than
leaving it as an opaque assumption.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryEpsilonElimination

variable {N : Type u}
variable {α : Type v}

/-- Binary grammar before non-start epsilon elimination. -/
structure BinaryNullableGrammar (N : Type u) (α : Type v) where
  terminalRule : N → α → Prop
  binaryRule : N → N → N → Prop
  epsilonRule : N → Prop
  unitRule : N → N → Prop

/-- Terminal derivation semantics of a binary/epsilon/unit grammar. -/
inductive BinaryNullableDerives
    (G : BinaryNullableGrammar N α) :
    N → List α → Prop
  | terminal
      {A : N} {a : α}
      (h : G.terminalRule A a) :
      BinaryNullableDerives G A [a]
  | epsilon
      {A : N}
      (h : G.epsilonRule A) :
      BinaryNullableDerives G A []
  | unit
      {A B : N} {w : List α}
      (h : G.unitRule A B)
      (d : BinaryNullableDerives G B w) :
      BinaryNullableDerives G A w
  | binary
      {A B C : N} {wB wC : List α}
      (h : G.binaryRule A B C)
      (dB : BinaryNullableDerives G B wB)
      (dC : BinaryNullableDerives G C wC) :
      BinaryNullableDerives G A (wB ++ wC)

/-- A nonterminal is nullable precisely when it derives epsilon. -/
def BinaryNullable
    (G : BinaryNullableGrammar N α)
    (A : N) : Prop :=
  BinaryNullableDerives G A []

/--
Unit rules present after epsilon elimination, with provenance retained so that
semantic reconstruction back into the original grammar is immediate.
-/
inductive EpsilonElimUnitRule
    (G : BinaryNullableGrammar N α) :
    N → N → Prop
  | original
      {A B : N}
      (h : G.unitRule A B) :
      EpsilonElimUnitRule G A B
  | dropLeft
      {A B C : N}
      (hbin : G.binaryRule A B C)
      (hnull : BinaryNullable G B) :
      EpsilonElimUnitRule G A C
  | dropRight
      {A B C : N}
      (hbin : G.binaryRule A B C)
      (hnull : BinaryNullable G C) :
      EpsilonElimUnitRule G A B

/--
Derivation semantics after deleting all epsilon rules.  Original terminal and
binary rules are unchanged; the unit relation is enlarged by nullable-child
deletions.
-/
inductive EpsilonFreeDerives
    (G : BinaryNullableGrammar N α) :
    N → List α → Prop
  | terminal
      {A : N} {a : α}
      (h : G.terminalRule A a) :
      EpsilonFreeDerives G A [a]
  | unit
      {A B : N} {w : List α}
      (h : EpsilonElimUnitRule G A B)
      (d : EpsilonFreeDerives G B w) :
      EpsilonFreeDerives G A w
  | binary
      {A B C : N} {wB wC : List α}
      (h : G.binaryRule A B C)
      (dB : EpsilonFreeDerives G B wB)
      (dC : EpsilonFreeDerives G C wC) :
      EpsilonFreeDerives G A (wB ++ wC)

/-- Epsilon-free derivations really are nonempty. -/
theorem epsilonFreeDerives_nonempty
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    (d : EpsilonFreeDerives G A w) :
    w ≠ [] := by
  induction d with
  | terminal _ =>
      simp
  | unit _ _ ih =>
      exact ih
  | binary _ _ _ ihB _ihC =>
      exact append_ne_nil_of_left_ne_nil ihB

/--
Forward simulation: every nonempty original derivation survives epsilon
elimination.
-/
theorem binaryNullableDerives_to_epsilonFree
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    (d : BinaryNullableDerives G A w) :
    w ≠ [] → EpsilonFreeDerives G A w := by
  induction d with
  | terminal h =>
      intro _hne
      exact EpsilonFreeDerives.terminal h

  | epsilon h =>
      intro hne
      exact False.elim (hne rfl)

  | @unit A B w h d ih =>
      intro hne
      exact EpsilonFreeDerives.unit
        (EpsilonElimUnitRule.original h)
        (ih hne)

  | @binary A B C wB wC h dB dC ihB ihC =>
      intro hne
      by_cases hB : wB = []
      · subst wB
        have hC : wC ≠ [] := by
          simpa using hne
        have dC' := ihC hC
        exact EpsilonFreeDerives.unit
          (EpsilonElimUnitRule.dropLeft h dB)
          dC'

      · by_cases hC : wC = []
        · subst wC
          have dB' := ihB hB
          simpa using
            (EpsilonFreeDerives.unit
              (EpsilonElimUnitRule.dropRight h dC)
              dB')
        · exact EpsilonFreeDerives.binary h (ihB hB) (ihC hC)

/--
Backward simulation: every epsilon-free derivation expands to an original
derivation by reinserting the nullable child witnessing each new unit rule.
-/
theorem epsilonFreeDerives_to_binaryNullable
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    (d : EpsilonFreeDerives G A w) :
    BinaryNullableDerives G A w := by
  induction d with
  | terminal h =>
      exact BinaryNullableDerives.terminal h

  | @unit A B w h d ih =>
      cases h with
      | original horig =>
          exact BinaryNullableDerives.unit horig ih
      | dropLeft hbin hnull =>
          simpa using
            (BinaryNullableDerives.binary hbin hnull ih)
      | dropRight hbin hnull =>
          simpa using
            (BinaryNullableDerives.binary hbin ih hnull)

  | binary h dB dC ihB ihC =>
      exact BinaryNullableDerives.binary h ihB ihC

/--
Exact preservation of every nonempty terminal language under binary-first
epsilon elimination.
-/
theorem epsilon_elimination_preserves_nonempty_language
    (G : BinaryNullableGrammar N α)
    (A : N)
    (w : List α)
    (hne : w ≠ []) :
    BinaryNullableDerives G A w ↔
      EpsilonFreeDerives G A w := by
  constructor
  · intro d
    exact binaryNullableDerives_to_epsilonFree G d hne
  · intro d
    exact epsilonFreeDerives_to_binaryNullable G d

/--
The nonempty language equality in the abstract interface used by
NormalizationLanguageBounds.
-/
theorem epsilon_elimination_sameNonemptyLanguage
    (G : BinaryNullableGrammar N α) :
    SameNonemptyLanguage
      (fun A => {w | BinaryNullableDerives G A w})
      (fun A => {w | EpsilonFreeDerives G A w}) := by
  intro A w hne
  exact epsilon_elimination_preserves_nonempty_language G A w hne

end BinaryEpsilonElimination

end TCS1
end LeanCfgProject
