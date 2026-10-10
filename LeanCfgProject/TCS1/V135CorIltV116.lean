import LeanCfgProject.TCS1.V135PolyBuildBridge
import LeanCfgProject.TCS1.V135MainTheoremItemIV

/-!
# TCS #1 v135: `cor:ilt` with the manuscript's v116 grammars as outputs

The verified materialized conservative learner keeps a finite sample
hypothesis `K_n = materializedConservativeHypothesis H datum n`; its
hypothesis grammar is `B_h(K_n)`, whose language is `BatchLanguage H K_n`.

Here the learner's *output* at stage `n` is the grammar code actually written
by the executable v116 constructor on (a duplicate-free listing of) `K_n`:

* `v116GrammarLearner_language`: the output grammar generates exactly
  `BatchLanguage H K_n`;
* `v116GrammarLearner_cost`: writing it takes at most `1400 (‖K_n‖ + 1)^4`
  counted steps (`thm_polyBuild`);
* `cor_ilt_v116`: on every positive presentation of an `H`-substitutable
  finite-CFG target, the output **grammar code itself** stabilizes and the
  stabilized grammar generates the target (Gold identification with
  syntactic convergence of the written grammar).

Listing the finite set `K_n` (`Finset.toList`) is used as a mathematical
function; the cost of maintaining the sample as a list is not counted.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section CorIltV116

variable {α : Type v} [Fintype α] [DecidableEq α]
variable {M : Type q} [Monoid M] [Fintype M] [DecidableEq M]

open PolyBuild

/-- The grammar code output at stage `n`. -/
noncomputable def v116GrammarLearner (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) (n : Nat) : V116GrammarCode α :=
  constructV116H H (materializedConservativeHypothesis H datum n).toList

theorem v116GrammarLearner_language (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) (n : Nat) :
    codeLanguage (v116GrammarLearner H datum n) =
      BatchLanguage H (materializedConservativeHypothesis H datum n) := by
  unfold v116GrammarLearner
  rw [constructV116H_language, Finset.toList_toFinset]

theorem v116GrammarLearner_cost (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) (n : Nat) :
    constructV116HCost H (materializedConservativeHypothesis H datum n).toList ≤
      1400 * (reconstructionSampleNorm
        (materializedConservativeHypothesis H datum n) + 1) ^ 4 := by
  have h := constructV116HCost_le H
    (Finset.nodup_toList (materializedConservativeHypothesis H datum n))
  rwa [Finset.toList_toFinset] at h

/-- Gold stabilization of the materialized learner transfers to the written
v116 grammar codes. -/
theorem v116GrammarLearner_stabilizes (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α)) (datum : Nat → Word α)
    (hgold : MaterializedGoldConclusion H L datum) :
    ∃ m, (∀ j, v116GrammarLearner H datum (m + j) = v116GrammarLearner H datum m) ∧
      codeLanguage (v116GrammarLearner H datum m) = L := by
  obtain ⟨n₀, h⟩ := hgold
  rcases h with ⟨hL, hstab⟩ | ⟨n, _, _, hL, hstab⟩
  · refine ⟨n₀, fun j => ?_, by rw [v116GrammarLearner_language, hL]⟩
    unfold v116GrammarLearner
    rw [hstab j]
  · refine ⟨n + 1, fun j => ?_, by rw [v116GrammarLearner_language, hL]⟩
    unfold v116GrammarLearner
    rw [hstab j]

/--
**`cor:ilt` (v135) with written v116 grammars.**  For every finite indexed CFG
target `L = L(G, S)` that is `H`-substitutable and every positive presentation
`datum` of `L` (every datum in `L`, every word of `L` eventually presented), the
sequence of grammar codes written by the v116 constructor on the learner's
samples is eventually constant, its limit generates exactly `L`, and each
output is written within `1400 (‖K_n‖ + 1)^4` counted steps.
-/
theorem cor_ilt_v116 {N : Type u} {P : Type w}
    [Fintype N] [Fintype P] [DecidableEq N]
    (H : FixedFiniteMonoidHom α M) (G : IndexedMixedCFG N α P) (S : N)
    (hsub : FixedHSubstitutable H (MixedNonterminalLanguage G.toMixedRules S))
    (datum : Nat → Word α)
    (hpos : ∀ n, datum n ∈ MixedNonterminalLanguage G.toMixedRules S)
    (hcov : ∀ x, x ∈ MixedNonterminalLanguage G.toMixedRules S →
      ∃ n, x ∈ concreteAccumulatedSample datum n) :
    (∃ m, (∀ j, v116GrammarLearner H datum (m + j) = v116GrammarLearner H datum m) ∧
      codeLanguage (v116GrammarLearner H datum m) =
        MixedNonterminalLanguage G.toMixedRules S) ∧
    ∀ n, constructV116HCost H (materializedConservativeHypothesis H datum n).toList ≤
      1400 * (reconstructionSampleNorm
        (materializedConservativeHypothesis H datum n) + 1) ^ 4 := by
  refine ⟨?_, v116GrammarLearner_cost H datum⟩
  have hEqL := leastClosedLanguage_eq_mixedNonterminalLanguage G.toMixedRules S
  have hsub' : FixedHSubstitutable H (LeastClosedLanguage G.toMixedRules S) := by
    rw [hEqL]; exact hsub
  have hpos' : ∀ n, datum n ∈ LeastClosedLanguage G.toMixedRules S := by
    intro n; rw [hEqL]; exact hpos n
  have hcov' : ∀ x, x ∈ LeastClosedLanguage G.toMixedRules S →
      ∃ n, x ∈ concreteAccumulatedSample datum n := by
    intro x hx; rw [hEqL] at hx; exact hcov x hx
  obtain ⟨_, _, _, hgold⟩ :=
    indexedFixedH_learning_materialized_core H G S hsub' datum hpos' hcov'
  rw [hEqL] at hgold
  exact v116GrammarLearner_stabilizes H _ datum hgold

end CorIltV116

end TCS1
end LeanCfgProject
