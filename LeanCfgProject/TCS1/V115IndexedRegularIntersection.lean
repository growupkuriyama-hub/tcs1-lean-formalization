import LeanCfgProject.TCS1.V115SSBNFRegularIntersection
import LeanCfgProject.TCS1.IndexedNormalizationLanguage

/-!
# TCS #1 v115: regular filtering of a finite indexed source CFG

Compose the explicit automaton-product SSBNF grammar with the
paper's verified normalization of an arbitrary finite indexed CFG.
The initial source symbol must have a nonempty successful yield:
this is exactly the constructive/productive normalization branch.
The epsilon word is separately preserved by the optional start rule.

There is no generic CFL-closure axiom here. The finite-state product
grammar is explicitly the output witness. The empty-only and empty
source-language cases of full Proposition 3.2(ii) remain separate
degenerate branches for the final unrestricted claim audit.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w x y

section V115IndexedRegularIntersection

variable {N : Type u} {α : Type v} {P : Type w}
variable {M : Type x} {F : Type y}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]
variable [Monoid M] [Fintype M]
variable [Monoid F] [Fintype F]

/--
Source-level Proposition 3.2(ii), on the nonempty-productive branch:
the filtered language has an explicit binary/terminal grammar with
non-start states (A,p,q), is exactly the original finite indexed CFG
language intersected with the finite-monoid recognized regular language,
and satisfies substitutability for H x G.
-/
theorem v115_indexedRegularIntersection_nonempty
    (R : IndexedMixedCFG N α P)
    (sourceStart : N)
    (hprod :
      ∃ w : Word α,
        w ∈ LeastClosedLanguage R.toMixedRules sourceStart
          ∧ w ≠ [])
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α F)
    (Acc : Set F)
    (hsub :
      FixedHSubstitutable
        H (LeastClosedLanguage R.toMixedRules sourceStart)) :
    let B := indexedFiniteFrontEndGrammar R
    let start := indexedProductiveUnitFreeState_of_nonempty
      R sourceStart hprod
    let t := reducedSSBNFTerminalRule B start
    let b := reducedSSBNFBinaryRule B start
    let s := reducedSSBNFStartRule B start
    let eps := [] ∈ LeastClosedLanguage R.toMixedRules sourceStart
    let filtered :=
      UntypedStartLanguage
        (v115FilterTerminal (v115MonoidTransition G) t)
        (v115FilterBinary b)
        (v115FilterStart s 1 (fun m => m ∈ Acc))
        (eps ∧ (1 : F) ∈ Acc)
    filtered =
      LeastClosedLanguage R.toMixedRules sourceStart
        ∩ RecognizedPreimage G Acc
    ∧
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G) filtered := by
  let B := indexedFiniteFrontEndGrammar R
  let start := indexedProductiveUnitFreeState_of_nonempty
    R sourceStart hprod
  let t := reducedSSBNFTerminalRule B start
  let b := reducedSSBNFBinaryRule B start
  let s := reducedSSBNFStartRule B start
  let eps := [] ∈ LeastClosedLanguage R.toMixedRules sourceStart
  let filtered :=
    UntypedStartLanguage
      (v115FilterTerminal (v115MonoidTransition G) t)
      (v115FilterBinary b)
      (v115FilterStart s 1 (fun m => m ∈ Acc))
      (eps ∧ (1 : F) ∈ Acc)
  change
    filtered =
      LeastClosedLanguage R.toMixedRules sourceStart
        ∩ RecognizedPreimage G Acc
    ∧
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G) filtered
  have hbase :
      UntypedStartLanguage t b s eps =
        LeastClosedLanguage R.toMixedRules sourceStart := by
    simpa only [t, b, s, B, start, eps] using
      (indexedReducedSSBNF_untypedStartLanguage_eq_source
        R sourceStart hprod)
  have hfilter :
      filtered =
        UntypedStartLanguage t b s eps
          ∩ RecognizedPreimage G Acc :=
    v115MonoidFilteredSSBNF_language G Acc t b s eps
  have hsubNorm :
      FixedHSubstitutable H
        (UntypedStartLanguage t b s eps) := by
    rw [hbase]
    exact hsub
  constructor
  · rw [hfilter, hbase]
  · exact
      v115_ssbnf_regular_filter_fixedH
        H G Acc t b s eps hsubNorm


/-- Degenerate terminal relation used for the empty/epsilon-only branch. -/
def v115TrivialTerminal {α : Type u} :
    Unit → α → Prop :=
  fun _ _ => False

/-- Degenerate binary relation used for the empty/epsilon-only branch. -/
def v115TrivialBinary :
    Unit → Unit → Unit → Prop :=
  fun _ _ _ => False

/-- No nonempty start branch in the degenerate grammar. -/
def v115TrivialStart :
    Unit → Prop :=
  fun _ => False

/-- The degenerate grammar generates exactly epsilon when eps holds. -/
theorem v115TrivialStartLanguage_iff
    {α : Type u}
    (eps : Prop)
    (word : Word α) :
    word ∈
      UntypedStartLanguage
        (v115TrivialTerminal (α := α))
        v115TrivialBinary
        v115TrivialStart
        eps
      ↔
    word = [] ∧ eps := by
  constructor
  · intro d
    cases d with
    | nonempty hstart _ =>
        exact False.elim hstart
    | epsilon heps =>
        exact ⟨rfl, heps⟩
  · rintro ⟨rfl, heps⟩
    exact UntypedStartDerives.epsilon heps

/--
The complementary source-CFG branch: if the source language contains no
nonempty word, the regular intersection is represented by the trivial
epsilon-only grammar above.  This covers both the empty language and {epsilon}.
-/
theorem v115_indexedRegularIntersection_no_nonempty
    (R : IndexedMixedCFG N α P)
    (sourceStart : N)
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α F)
    (Acc : Set F)
    (hno :
      ∀ w : Word α,
        w ∈ LeastClosedLanguage R.toMixedRules sourceStart →
        w = [])
    (hsub :
      FixedHSubstitutable
        H (LeastClosedLanguage R.toMixedRules sourceStart)) :
    let eps :=
      ([] : Word α) ∈
        LeastClosedLanguage R.toMixedRules sourceStart
        ∧ (1 : F) ∈ Acc
    let filtered :=
      UntypedStartLanguage
        (v115TrivialTerminal (α := α))
        v115TrivialBinary
        v115TrivialStart
        eps
    filtered =
      LeastClosedLanguage R.toMixedRules sourceStart
        ∩ RecognizedPreimage G Acc
    ∧
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G) filtered := by
  let eps :=
    ([] : Word α) ∈
      LeastClosedLanguage R.toMixedRules sourceStart
      ∧ (1 : F) ∈ Acc
  let filtered :=
    UntypedStartLanguage
      (v115TrivialTerminal (α := α))
      v115TrivialBinary
      v115TrivialStart
      eps
  change
    filtered =
      LeastClosedLanguage R.toMixedRules sourceStart
        ∩ RecognizedPreimage G Acc
    ∧
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G) filtered
  have heq :
      filtered =
        LeastClosedLanguage R.toMixedRules sourceStart
          ∩ RecognizedPreimage G Acc := by
    apply Set.ext
    intro word
    constructor
    · intro hw
      have hshape :=
        (v115TrivialStartLanguage_iff
          (α := α) eps word).mp hw
      rcases hshape with ⟨rfl, heps⟩
      constructor
      · exact heps.1
      · change G.h ([] : Word α) ∈ Acc
        simpa only [G.map_nil] using heps.2
    · rintro ⟨hsrc, hreg⟩
      have hnil : word = [] :=
        hno word hsrc
      subst word
      apply
        (v115TrivialStartLanguage_iff
          (α := α) eps []).mpr
      constructor
      · rfl
      · constructor
        · exact hsrc
        · change G.h ([] : Word α) ∈ Acc at hreg
          simpa only [G.map_nil] using hreg
  constructor
  · exact heq
  · rw [heq]
    exact
      fixedHSubstitutable_inter_recognized_product
        H G Acc hsub


/--
Exhaustive source-level split for Proposition 3.2(ii).
Either the source start has a nonempty successful yield and the normalized
DFA-product grammar applies, or every successful word is epsilon and the
trivial grammar applies.  These alternatives cover all finite indexed CFGs.
-/
theorem v115_indexedRegularIntersection_exhaustive
    (R : IndexedMixedCFG N α P)
    (sourceStart : N)
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α F)
    (Acc : Set F)
    (hsub :
      FixedHSubstitutable
        H (LeastClosedLanguage R.toMixedRules sourceStart)) :
    (∃ hprod :
        ∃ w : Word α,
          w ∈ LeastClosedLanguage R.toMixedRules sourceStart
            ∧ w ≠ [],
      let B := indexedFiniteFrontEndGrammar R
      let start := indexedProductiveUnitFreeState_of_nonempty
        R sourceStart hprod
      let t := reducedSSBNFTerminalRule B start
      let b := reducedSSBNFBinaryRule B start
      let s := reducedSSBNFStartRule B start
      let eps := [] ∈ LeastClosedLanguage R.toMixedRules sourceStart
      let filtered :=
        UntypedStartLanguage
          (v115FilterTerminal (v115MonoidTransition G) t)
          (v115FilterBinary b)
          (v115FilterStart s 1 (fun m => m ∈ Acc))
          (eps ∧ (1 : F) ∈ Acc)
      filtered =
        LeastClosedLanguage R.toMixedRules sourceStart
          ∩ RecognizedPreimage G Acc
      ∧
      FixedHSubstitutable
        (productFixedFiniteMonoidHom H G) filtered)
    ∨
    (let eps :=
        ([] : Word α) ∈
          LeastClosedLanguage R.toMixedRules sourceStart
          ∧ (1 : F) ∈ Acc
     let filtered :=
        UntypedStartLanguage
          (v115TrivialTerminal (α := α))
          v115TrivialBinary
          v115TrivialStart
          eps
     filtered =
       LeastClosedLanguage R.toMixedRules sourceStart
         ∩ RecognizedPreimage G Acc
     ∧
     FixedHSubstitutable
       (productFixedFiniteMonoidHom H G) filtered) := by
  classical
  by_cases hprod :
      ∃ w : Word α,
        w ∈ LeastClosedLanguage R.toMixedRules sourceStart
          ∧ w ≠ []
  · exact
      Or.inl
        ⟨hprod,
          v115_indexedRegularIntersection_nonempty
            R sourceStart hprod H G Acc hsub⟩
  · have hno :
        ∀ w : Word α,
          w ∈ LeastClosedLanguage R.toMixedRules sourceStart →
          w = [] := by
      intro w hw
      by_contra hwne
      exact hprod ⟨w, hw, hwne⟩
    exact
      Or.inr
        (v115_indexedRegularIntersection_no_nonempty
          R sourceStart H G Acc hno hsub)

end V115IndexedRegularIntersection

end TCS1
end LeanCfgProject
