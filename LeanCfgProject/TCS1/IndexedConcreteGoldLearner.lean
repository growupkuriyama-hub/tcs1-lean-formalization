import LeanCfgProject.TCS1.IndexedSection7Bridge
import LeanCfgProject.TCS1.ConcreteConservativeLearner

/-!
# TCS #1: fully concrete indexed fixed-window Gold learner

This module removes the remaining abstract-run parameters from the source-level
Gold theorem.  The learner is now the concrete conservative reconstruction
sequence itself: a hypothesis is the finite sample used to build
`BatchLanguage`, generated data are kept, and missing data trigger rebuilding
from the full accumulated positive sample.

The only text assumptions left are the standard positive-presentation
conditions: every datum belongs to the target and every target word eventually
appears in the accumulated sample.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedConcreteGoldLearner

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/-- The indexed normalization scale is automatically positive once a source
start nonterminal has been chosen. -/
theorem indexedNormalizationScale_pos_of_start
    (G : IndexedMixedCFG N α P)
    (A : N) :
    0 < G.normalizationScale := by
  have hN : 0 < Fintype.card N :=
    Fintype.card_pos_iff.mpr ⟨A⟩
  unfold IndexedMixedCFG.normalizationScale
  omega

/--
End-to-end identification by the concrete conservative learner under the
paper's fixed-h substitutability hypothesis.
-/
theorem indexedFixedWindow_concreteGold_identification
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR k l : Nat)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
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
        (fixedWindowMonoidHom (α := α) k l)
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
  have hpack :=
    indexedFixedWindowSection7_package
      G A hprod τR k l
      (indexedNormalizationScale_pos_of_start G A)
      hsource hsub
  exact
    concreteConservative_gold_identification
      (fixedWindowMonoidHom (α := α) k l)
      (LeastClosedLanguage G.toMixedRules A)
      (indexedFixedWindowCanonicalSample
        G A hprod k l)
      hpack.1 hsub
      datum hpositive hcoverage

/--
Classical Yoshinaka (k,l)-substitutability form of the fully concrete learner.
-/
theorem indexedClassicalFixedWindow_concreteGold_identification
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR k l : Nat)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hwin :
      FixedWindowSubstitutable
        k l
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
        (fixedWindowMonoidHom (α := α) k l)
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
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (LeastClosedLanguage G.toMixedRules A) :=
    fixedHSubstitutable_of_fixedWindowSubstitutable
      k l
      (LeastClosedLanguage G.toMixedRules A)
      hwin
  exact
    indexedFixedWindow_concreteGold_identification
      G A hprod τR k l hsource hsub
      datum hpositive hcoverage

/-- Fully concrete learner at the explicit (0,0) endpoint. -/
theorem indexedZeroWindow_concreteGold_identification
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR : Nat)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hzero :
      NonemptyFactorSubstitutable
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
        (fixedWindowMonoidHom (α := α) 0 0)
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
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) 0 0)
        (LeastClosedLanguage G.toMixedRules A) :=
    (fixedHSubstitutable_zeroWindow_iff_nonemptyFactorSubstitutable
      (α := α)
      (LeastClosedLanguage G.toMixedRules A)).2 hzero
  exact
    indexedFixedWindow_concreteGold_identification
      G A hprod τR 0 0 hsource hsub
      datum hpositive hcoverage

end IndexedConcreteGoldLearner

end TCS1
end LeanCfgProject
