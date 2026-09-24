import LeanCfgProject.TCS1.IndexedNormalizationLanguage
import LeanCfgProject.TCS1.FixedWindowCharacteristicDataFacade
import LeanCfgProject.TCS1.ConcreteConservativeLearner
import LeanCfgProject.TCS1.TrivialTargetEndpoints

/-!
# TCS #1: qualitative indexed fixed-h reconstruction and Gold learning

The fixed-window development is a quantitative specialization.  The main
qualitative theorem of the paper is more general: for an arbitrary fixed finite
monoid homomorphism h, a finite canonical witness sample suffices for exact
reconstruction.

This module connects that theorem directly to a finite indexed source CFG.
No fixed-window hypothesis, source thickness parameter, or normalization-size
bound is needed.  The source grammar is normalized semantically, the generic
fixed-h canonical sample is taken on the resulting reduced start-separated
grammar, and exact reconstruction is transported back to the original source
language.  The same sample then feeds the concrete conservative Gold learner.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section IndexedFixedHBridge

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {M : Type q}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]
variable [Monoid M] [Fintype M]

/-- Generic fixed-h canonical sample of the actual normalized indexed grammar. -/
noncomputable def indexedFixedHCanonicalSample
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :
    Finset (Word α) := by
  classical
  let start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G) :=
    indexedProductiveUnitFreeState_of_nonempty
      G A hprod
  let Nf :=
    ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G) start
  letI : Fintype Nf := Fintype.ofFinite _
  exact
    fixedWindowMinimalCanonicalSample
      H
      (reducedSSBNFTerminalRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFBinaryRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFStartRule
        (indexedFiniteFrontEndGrammar G) start)
      ([] ∈ LeastClosedLanguage G.toMixedRules A)

/--
Exact source-language reconstruction for an arbitrary fixed finite-monoid
typing.  This is the qualitative source-CFG form of the main reconstruction
theorem, with Appendix-A normalization discharged internally.
-/
theorem indexedFixedHCanonicalSample_characteristic
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    BatchLanguage H
        (indexedFixedHCanonicalSample H G A hprod)
      =
    LeastClosedLanguage G.toMixedRules A := by
  classical
  let start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G) :=
    indexedProductiveUnitFreeState_of_nonempty
      G A hprod
  let Nf :=
    ReducedUnitFreeState
      (indexedFiniteFrontEndGrammar G) start
  letI : Fintype Nf := Fintype.ofFinite _

  have hlang :
      UntypedStartLanguage
        (reducedSSBNFTerminalRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFBinaryRule
          (indexedFiniteFrontEndGrammar G) start)
        (reducedSSBNFStartRule
          (indexedFiniteFrontEndGrammar G) start)
        ([] ∈ LeastClosedLanguage G.toMixedRules A)
        =
      LeastClosedLanguage G.toMixedRules A := by
    simpa [start] using
      indexedReducedSSBNF_untypedStartLanguage_eq_source
        G A hprod

  have hsub' :
      FixedHSubstitutable H
        (UntypedStartLanguage
          (reducedSSBNFTerminalRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFBinaryRule
            (indexedFiniteFrontEndGrammar G) start)
          (reducedSSBNFStartRule
            (indexedFiniteFrontEndGrammar G) start)
          ([] ∈ LeastClosedLanguage G.toMixedRules A)) := by
    rw [hlang]
    exact hsub

  have hchar :=
    fixedWindowMinimalCanonicalSample_characteristic_untyped
      H
      (reducedSSBNFTerminalRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFBinaryRule
        (indexedFiniteFrontEndGrammar G) start)
      (reducedSSBNFStartRule
        (indexedFiniteFrontEndGrammar G) start)
      ([] ∈ LeastClosedLanguage G.toMixedRules A)
      hsub'

  rw [hlang] at hchar
  simpa [indexedFixedHCanonicalSample, Nf, start] using hchar

/--
Concrete conservative Gold identification for the arbitrary fixed-h source
theorem.  The only text assumptions are positivity and coverage.
-/
theorem indexedFixedH_concreteGold_identification
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
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
    let R :=
      concreteAccumulatedConservativeRun
        H
        (LeastClosedLanguage G.toMixedRules A)
        datum hpositive
    ∃ n₀,
      (R.lang (R.hyp n₀) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        R.hyp (n + 1) ≠ R.hyp n ∧
        R.lang (R.hyp (n + 1)) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j,
          R.hyp ((n + 1) + j) =
            R.hyp (n + 1)) := by
  exact
    concreteConservative_gold_identification
      H
      (LeastClosedLanguage G.toMixedRules A)
      (indexedFixedHCanonicalSample H G A hprod)
      (indexedFixedHCanonicalSample_characteristic
        H G A hprod hsub)
      hsub
      datum hpositive hcoverage


/--
Full source-level Gold theorem for every nonempty target language.

The earlier source bridge chooses a non-start symbol with a nonempty terminal
yield.  If no such word exists, nonemptiness forces the source language to be
exactly {lambda}, which is handled by the separately verified endpoint.
Thus the nonempty-target statement now matches the paper's text convention
without an extra productivity-side condition in its interface.
-/
theorem indexedFixedH_concreteGold_identification_nonempty
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
    ∃ n₀,
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
            concreteConservativeHypothesis H datum (n + 1)) := by
  classical
  by_cases hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []
  · exact
      concreteConservative_gold_identification_explicit
        H
        (LeastClosedLanguage G.toMixedRules A)
        (indexedFixedHCanonicalSample H G A hprod)
        (indexedFixedHCanonicalSample_characteristic
          H G A hprod hsub)
        hsub
        datum hpositive hcoverage
  · have hL :
        LeastClosedLanguage G.toMixedRules A
          =
        ({[]} : Set (Word α)) := by
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
        subst w
        obtain ⟨z, hz⟩ := hnonempty
        have hz0 : z = [] := by
          by_contra hzne
          exact hprod ⟨z, hz, hzne⟩
        simpa [hz0] using hz

    have hpositive' :
        ∀ n, datum n ∈ ({[]} : Set (Word α)) := by
      intro n
      rw [← hL]
      exact hpositive n

    have hcoverage' :
        ∀ word,
          word ∈ ({[]} : Set (Word α)) →
          ∃ n,
            word ∈ concreteAccumulatedSample datum n := by
      intro word hw
      apply hcoverage word
      rw [hL]
      exact hw

    have heps :=
      concreteConservative_gold_identification_explicit
        H
        ({[]} : Set (Word α))
        ({[]} : Finset (Word α))
        (singletonEpsilon_characteristic H)
        (singletonEpsilon_fixedHSubstitutable H)
        datum hpositive' hcoverage'

    simpa [hL] using heps

end IndexedFixedHBridge

end TCS1
end LeanCfgProject
