import LeanCfgProject.TCS1.V158CostedLearnerCharacteristic

/-!
# TCS #1 v158: `thm:main`(iii) for one executable learner

`thm:main`(iii): "*`A_h` identifies every nonempty `L ∈ C^cf_h` in Gold's sense,
each update taking time polynomial in the data seen so far*", with `A_h` a
conservative sequential learner built on the set-driven operator `B_h`.

`thm_main_item_iii_executable` states, for the **same** executable learner
`CostedLearner.stateAt` (explicit lists, every operation counted):
1. its written grammar at stage `n` generates `L(B_h(K_n))` for the semantic
   conservative hypothesis `K_n` (set-driven semantics; the list order of the
   stored sample is not canonical, the language is);
2. conservativeness: a generated datum leaves the written grammar unchanged;
3. Gold identification with syntactic stabilization of the written grammar;
4. every update costs at most `4·10¹⁶ · (P + 1)^20` steps, `P` the encoded size
   of the data seen so far.
-/

namespace LeanCfgProject
namespace TCS1
namespace CostedLearner

open PolyBuild

universe u v w q

theorem thm_main_item_iii_executable
    {α : Type v} [Fintype α] [DecidableEq α]
    {M : Type q} [Monoid M] [Fintype M] [DecidableEq M]
    (H : FixedFiniteMonoidHom α M)
    {N : Type u} {P : Type w} [Fintype N] [Fintype P] [DecidableEq N]
    (G : IndexedMixedCFG N α P) (S : N)
    (hsub : FixedHSubstitutable H (MixedNonterminalLanguage G.toMixedRules S))
    (datum : Nat → Word α)
    (hpos : ∀ n, datum n ∈ MixedNonterminalLanguage G.toMixedRules S)
    (hcov : ∀ x, x ∈ MixedNonterminalLanguage G.toMixedRules S →
      ∃ n, x ∈ concreteAccumulatedSample datum n) :
    (∀ n, codeLanguage (stateAt H datum n).code =
      BatchLanguage H (materializedConservativeHypothesis H datum n))
    ∧ (∀ n, datum (n + 1) ∈ codeLanguage (stateAt H datum n).code →
        (stateAt H datum (n + 1)).code = (stateAt H datum n).code)
    ∧ (∃ m, (∀ j, (stateAt H datum (m + j)).code = (stateAt H datum m).code) ∧
        codeLanguage (stateAt H datum m).code = MixedNonterminalLanguage G.toMixedRules S)
    ∧ (∀ n, updateCost H datum n ≤
        40000000000000000 * (positiveDataPrefixNorm datum (n + 1) + 1) ^ 20) := by
  refine ⟨code_language H datum, ?_, costedLearner_gold H G S hsub datum hpos hcov,
    updateCost_le H datum⟩
  intro n hn
  exact (updateC_conservative H _ _ hn).1

end CostedLearner
end TCS1
end LeanCfgProject
