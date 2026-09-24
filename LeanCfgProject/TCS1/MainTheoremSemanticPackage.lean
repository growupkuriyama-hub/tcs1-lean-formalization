import LeanCfgProject.TCS1.IndexedFixedHBridge
import LeanCfgProject.TCS1.IndexedLinearCharacteristicData
import LeanCfgProject.TCS1.FixedWindowSection7Package

/-!
# TCS #1 v79: paper-facing semantic package for the main theorem

The manuscript's main theorem combines three logically different layers:

1. sample consistency / sound reconstruction;
2. existence of finite characteristic data and Gold identification;
3. polynomial construction/update bounds and the two quantitative
   specializations (fixed windows and linear targets).

The algorithmic running-time claims are intentionally kept in the dedicated
complexity modules.  This file closes the *semantic* theorem surface directly
over an arbitrary finite indexed source CFG and removes endpoint side
conditions from the characteristic-sample statement.

In particular, every fixed-h substitutable source language represented by a
finite indexed CFG has a finite positive characteristic sample:
* a productive nonempty branch uses the canonical normalized witness sample;
* the epsilon-only endpoint uses {epsilon};
* the empty endpoint uses the empty sample.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section MainTheoremSemanticPackage

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {M : Type q}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]
variable [Monoid M] [Fintype M]

/--
Every fixed-h substitutable finite indexed CFG target has a finite positive
characteristic sample for the set-driven reconstruction operator.

Unlike the lower-level source bridge, this theorem has no productivity or
nonemptiness side condition: empty and epsilon-only targets are discharged
explicitly.
-/
theorem indexedFixedH_exists_characteristic_sample
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    ∃ C : Finset (Word α),
      (↑C : Set (Word α)) ⊆
        LeastClosedLanguage G.toMixedRules A
      ∧
      BatchLanguage H C =
        LeastClosedLanguage G.toMixedRules A := by
  classical
  let L : Set (Word α) :=
    LeastClosedLanguage G.toMixedRules A
  by_cases hprod :
      ∃ u : Word α, u ∈ L ∧ u ≠ []
  · let C :=
      indexedFixedHCanonicalSample
        H G A hprod
    have hchar :
        BatchLanguage H C = L := by
      simpa [L, C] using
        indexedFixedHCanonicalSample_characteristic
          H G A hprod hsub
    refine ⟨C, ?_, hchar⟩
    intro w hw
    have hcons :
        w ∈ BatchLanguage H C :=
      sample_consistency H C hw
    rw [hchar] at hcons
    exact hcons
  · by_cases heps : ([] : Word α) ∈ L
    · have hL :
          L = ({[]} : Set (Word α)) := by
        apply Set.ext
        intro w
        constructor
        · intro hw
          have hw0 : w = [] := by
            by_contra hne
            exact hprod ⟨w, hw, hne⟩
          simpa [hw0]
        · intro hw
          have hw0 : w = [] := by
            simpa using hw
          simpa [hw0] using heps
      refine ⟨{[]}, ?_, ?_⟩
      · intro w hw
        have hw0 : w = [] := by
          simpa using hw
        subst w
        simpa [L] using heps
      · rw [show
          LeastClosedLanguage G.toMixedRules A = L by rfl]
        rw [hL]
        exact singletonEpsilon_characteristic H
    · have hL :
          L = (∅ : Set (Word α)) := by
        apply Set.ext
        intro w
        constructor
        · intro hw
          have hw0 : w = [] := by
            by_contra hne
            exact hprod ⟨w, hw, hne⟩
          subst w
          exact False.elim (heps hw)
        · intro hw
          simp at hw
      refine ⟨∅, ?_, ?_⟩
      · intro w hw
        simp at hw
      · rw [show
          LeastClosedLanguage G.toMixedRules A = L by rfl]
        rw [hL]
        exact batchLanguage_empty_eq H

/--
Qualitative semantic core of the paper's Fixed-h Learning Theorem for a
concrete finite indexed CFG target.

The three conjuncts are:
1. sample consistency of the reconstruction operator;
2. existence of finite positive characteristic data;
3. conservative Gold identification for every nonempty target text.

Polynomial construction/update time and the fixed-window/linear quantitative
data bounds are verified in their dedicated theorem packages.
-/
theorem indexedFixedH_learning_semantic_core
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hnonempty :
      ∃ w : Word α,
        w ∈ LeastClosedLanguage G.toMixedRules A)
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A))
    (datum : Nat → Word α)
    (hpositive :
      ∀ n,
        datum n ∈ LeastClosedLanguage G.toMixedRules A)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules A →
        ∃ n,
          word ∈ concreteAccumulatedSample datum n) :
    (∀ K : Finset (Word α),
      (↑K : Set (Word α)) ⊆ BatchLanguage H K)
    ∧
    (∃ C : Finset (Word α),
      (↑C : Set (Word α)) ⊆
        LeastClosedLanguage G.toMixedRules A
      ∧
      BatchLanguage H C =
        LeastClosedLanguage G.toMixedRules A)
    ∧
    (∃ n₀,
      (BatchLanguage H
          (concreteConservativeHypothesis H datum n₀)
          =
        LeastClosedLanguage G.toMixedRules A
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum (n₀ + j) =
            concreteConservativeHypothesis H datum n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        concreteConservativeHypothesis H datum (n + 1) ≠
          concreteConservativeHypothesis H datum n ∧
        BatchLanguage H
          (concreteConservativeHypothesis H datum (n + 1))
          =
        LeastClosedLanguage G.toMixedRules A
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum ((n + 1) + j) =
            concreteConservativeHypothesis H datum (n + 1))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro K
    exact sample_consistency H K
  · exact
      indexedFixedH_exists_characteristic_sample
        H G A hsub
  · exact
      indexedFixedH_concreteGold_identification_nonempty
        H G A hnonempty hsub datum hpositive hcoverage

end MainTheoremSemanticPackage

end TCS1
end LeanCfgProject
