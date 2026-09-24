import LeanCfgProject.TCS1.LinearMixedRhsDecomposition
import LeanCfgProject.TCS1.FiniteCFGEncoding

/-!
# TCS #1: raw linear indexed grammars before epsilon/unit preprocessing

The specialized linear normalization currently starts after empty and unit
productions have been removed.  This module moves one stage to the left.

Any mixed right-hand side containing at most one nonterminal has exactly one
of the three shapes relevant to the standard linear preprocessing:

* epsilon;
* a unit production B; or
* a nonempty, non-unit prepared linear right-hand side.

We choose such a shape for every production of an ordinary finite indexed
linear CFG and prove exact one-step semantics and least-language preservation.
This representation is the input for the explicit epsilon/unit elimination
bridge.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearRawPreprocessing

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- Raw linear right-hand sides, before epsilon and unit elimination. -/
inductive RawLinearRhs
    (N : Type u)
    (α : Type v)
  | epsilon
  | unit (B : N)
  | prepared (rhs : PreparedLinearRhs N α)

/-- Recover the ordinary mixed-symbol right-hand side. -/
def RawLinearRhs.toMixedRhs :
    RawLinearRhs N α → List (MixedSymbol N α)
  | .epsilon => []
  | .unit B => [Sum.inl B]
  | .prepared rhs => rhs.toMixedRhs

/-- Semantics of a raw linear right-hand side under a nonterminal family. -/
def RawLinearRhs.realizes
    (L : N → Set (List α)) :
    RawLinearRhs N α → List α → Prop
  | .epsilon, word =>
      word = []
  | .unit B, word =>
      word ∈ L B
  | .prepared rhs, word =>
      PreparedLinearRhs.realizes L rhs word

/--
Every linear mixed RHS has a raw representation.  Empty and singleton-unit
cases are split off; every other linear RHS is already a prepared RHS.
-/
theorem exists_rawLinearRhs_of_linear
    (rhs : List (MixedSymbol N α))
    (hlin : MixedRhsLinear rhs) :
    ∃ raw : RawLinearRhs N α,
      raw.toMixedRhs = rhs := by
  by_cases hempty : rhs = []
  · subst rhs
    exact ⟨RawLinearRhs.epsilon, rfl⟩
  · by_cases hunit :
        ∃ B : N, rhs = [Sum.inl B]
    · rcases hunit with ⟨B, rfl⟩
      exact ⟨RawLinearRhs.unit B, rfl⟩
    · have hnonunit :
          ∀ B : N, rhs ≠ [Sum.inl B] := by
        intro B hEq
        exact hunit ⟨B, hEq⟩
      obtain ⟨prepared, hprepared⟩ :=
        exists_preparedLinearRhs_of_linear_nonempty_nonunit
          rhs hlin hempty hnonunit
      exact
        ⟨RawLinearRhs.prepared prepared,
          hprepared⟩

/-- Raw and ordinary mixed RHS semantics agree exactly. -/
theorem rawLinearRhs_realizes_iff_mixed
    (L : N → Set (List α))
    (raw : RawLinearRhs N α)
    (word : List α) :
    RawLinearRhs.realizes L raw word
      ↔
    RhsRealizes L raw.toMixedRhs word := by
  cases raw with
  | epsilon =>
      change word = [] ↔ RhsRealizes L [] word
      constructor
      · intro h
        subst word
        rfl
      · intro h
        exact h
  | unit B =>
      change word ∈ L B ↔
        RhsRealizes L [Sum.inl B] word
      constructor
      · intro h
        exact ⟨word, [], by simp, h, rfl⟩
      · rintro ⟨left, right, hword, hleft, hright⟩
        have hrightNil : right = [] := hright
        subst right
        have hw : word = left := by
          simpa using hword
        rw [hw]
        exact hleft
  | prepared rhs =>
      exact
        preparedLinearRhs_realizes_iff_mixed
          L rhs word

/-- Finite indexed raw linear grammar. -/
structure RawLinearIndexedCFG
    (N : Type u)
    (α : Type v)
    (P : Type w) where
  lhs : P → N
  rhs : P → RawLinearRhs N α

/-- Closure under all raw linear source productions. -/
def RawLinearGrammarClosed
    (G : RawLinearIndexedCFG N α P)
    (L : N → Set (List α)) : Prop :=
  ∀ p : P, ∀ word : List α,
    RawLinearRhs.realizes L (G.rhs p) word →
    word ∈ L (G.lhs p)

/-- Least generated language of a raw linear grammar. -/
def RawLinearLeastLanguage
    (G : RawLinearIndexedCFG N α P)
    (A : N) :
    Set (List α) :=
  {word |
    ∀ L : N → Set (List α),
      RawLinearGrammarClosed G L →
      word ∈ L A}

/-- An ordinary indexed grammar is syntactically linear production by production. -/
def IndexedMixedCFG.IsLinear
    (G : IndexedMixedCFG N α P) : Prop :=
  ∀ p : P, MixedRhsLinear (G.rhs p)

/-- Chosen raw RHS for one production of an indexed linear grammar. -/
noncomputable def indexedRawLinearRhs
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (p : P) :
    RawLinearRhs N α :=
  Classical.choose
    (exists_rawLinearRhs_of_linear
      (G.rhs p) (hlinear p))

@[simp] theorem indexedRawLinearRhs_toMixed
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (p : P) :
    (indexedRawLinearRhs G hlinear p).toMixedRhs =
      G.rhs p := by
  exact
    Classical.choose_spec
      (exists_rawLinearRhs_of_linear
        (G.rhs p) (hlinear p))

/-- Raw indexed presentation chosen from the ordinary indexed linear CFG. -/
noncomputable def IndexedMixedCFG.toRawLinear
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear) :
    RawLinearIndexedCFG N α P where
  lhs := G.lhs
  rhs := indexedRawLinearRhs G hlinear

/--
Raw closure is exactly ordinary mixed-CFG closure for the original indexed
linear grammar.
-/
theorem indexedMixedCFG_rawClosed_iff_grammarClosed
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (L : N → Set (List α)) :
    RawLinearGrammarClosed
        (G.toRawLinear hlinear) L
      ↔
    GrammarClosed G.toMixedRules L := by
  constructor
  · intro hraw A word hstep
    rcases hstep with
      ⟨rhs, ⟨p, hlhs, hrhs⟩, hreal⟩
    subst A
    apply hraw p word
    apply
      (rawLinearRhs_realizes_iff_mixed
        L ((G.toRawLinear hlinear).rhs p) word).2
    change
      RhsRealizes L
        (indexedRawLinearRhs G hlinear p).toMixedRhs
        word
    rw [indexedRawLinearRhs_toMixed]
    rw [hrhs]
    exact hreal
  · intro hclosed p word hreal
    apply hclosed (G.lhs p)
    refine ⟨G.rhs p, ?_, ?_⟩
    · exact ⟨p, rfl, rfl⟩
    · have hmixed :=
        (rawLinearRhs_realizes_iff_mixed
          L ((G.toRawLinear hlinear).rhs p) word).1
          hreal
      change
        RhsRealizes L
          (indexedRawLinearRhs G hlinear p).toMixedRhs
          word at hmixed
      rw [indexedRawLinearRhs_toMixed] at hmixed
      exact hmixed

/-- Least languages are preserved exactly by the raw representation. -/
theorem indexedMixedCFG_rawLeast_eq_source
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (A : N) :
    RawLinearLeastLanguage
        (G.toRawLinear hlinear) A
      =
    LeastClosedLanguage G.toMixedRules A := by
  apply Set.ext
  intro word
  constructor
  · intro hraw L hclosed
    exact
      hraw L
        ((indexedMixedCFG_rawClosed_iff_grammarClosed
          G hlinear L).2 hclosed)
  · intro hsource L hclosed
    exact
      hsource L
        ((indexedMixedCFG_rawClosed_iff_grammarClosed
          G hlinear L).1 hclosed)

end LinearRawPreprocessing

end TCS1
end LeanCfgProject
