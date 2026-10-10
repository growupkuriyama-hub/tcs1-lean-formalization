# TCS #1 v158 — `thm:main`(iii) / `cor:ilt`: one executable learner, Gold identification, counted update time (2026-10-10)

> **Manuscript.** v158, `thm:main`(iii): "*`A_h` identifies every nonempty `L ∈ C^cf_h` in Gold's sense, each update taking time polynomial in the data seen so far*". `cor:ilt`: "*once `WitnessSet(G̃) ⊆ K_{n₀}`, among stages `n ≥ n₀` at most one hypothesis change can occur*".
> **CI.** New V158 theorems verified in CI #1044 (`5207728`, DPDA), CI #1048 (`783bf83`, CYK and learner) and `d95c5af0c6e672cb65214e8760a3e2ff39ace387` — [CI #1050](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38053099704) SUCCESS (all 5 gates, including the V158 `#guard_msgs` axiom audit). `V158ObstructionSet` was added in the final commit.

## 1. Gap before this session

* The v116 constructor was executable and step-counted (`thm_polyBuild`, ≤ `1400(‖K‖+1)^4`).
* The v79 learner's update "cost" was an **envelope**: a count of finite candidate spaces, not a counted run of an executable function.
* `cor_ilt_v116` used `Finset.toList` and charged nothing for:
  - maintaining the sample;
  - the duplicate test;
  - the membership test on the written grammar.

## 2. Implementation

### `V158CodeCYK.lean`: costed membership on the written v116 code

* `codeMemberC c w`:
  - **Atoms** are triples `(x, i, j)`.
  - **Horn clauses** come from the lexical, unary and binary rules, over all spans and splits of `w`.
  - **Chart:** `Horn.hornC`, the step-counted Horn engine of `V144HornClosure`.
  - **Acceptance:** a start name `x` with `(x, 0, |w|)` in the chart, or `w = []` with the ε flag set.
* **Atom comparison:** names are compared letter by letter (`eqC`), plus 2 steps for the indices.
* **Correctness:** `codeMemberC_correct : (codeMemberC c w).1 = true ↔ w ∈ codeLanguage c`, via `mem_chart_iff`. The chart is exactly the set of derivable spans of `codeGrammar c`.
* **Cost:** `codeMemberC_cost_le : (codeMemberC c w).2 ≤ 2·10⁶ · (C+1)³ · (|w|+1)⁷ · (Λ+4)`.
  - `C` bounds every rule list of the code; `Λ` bounds every name length.

### `V158CostedLearner.lean`: learner state and update

* **State:** `State = ⟨data, cur, code⟩`, all explicit lists.
* **One update, `updateC H s w`, every operation counted:**
  1. `codeMemberC s.code w`: membership in the current written grammar.
  2. `wordMemC w s.data`: duplicate test, letter by letter.
  3. `appendC s.data [w]`: append if new, one step per copied cell.
  4. Keep, or rebuild: `cur := data'` (shared, not copied), then the code is rewritten by `constructV116C`.
* **No `Finset` operation and no `Finset.toList`.**

## 3. Theorems

| | theorem | statement |
|---|---|---|
| invariant | `stateAt_spec` | `data` lists `concreteAccumulatedSample datum n` without duplicates; `cur` lists `materializedConservativeHypothesis H datum n` without duplicates; `code = constructV116H H cur` |
| semantics | `code_language` | `codeLanguage (stateAt n).code = BatchLanguage H K_n` |
| conservative | `updateC_conservative` | a generated datum leaves `code` and `cur` unchanged |
| Gold | `costedLearner_gold` | the written code stabilizes **syntactically**; its language is the target (transferred from `indexedFixedH_learning_materialized_core`) |
| `cor:ilt` precise | `costedLearner_at_most_one_change` | if a characteristic `C` (`C ⊆ L`, `BatchLanguage H C = L`) is contained in the data by stage `n₀`, then after the first change of the written code at a stage `n+1 ≥ n₀ + 1`, the code never changes again (via `ConservativeGoldKernel`) |
| cost | `updateC_cost_le`, `updateCost_le` | each update costs at most `4·10¹⁶ · (P+1)^20` steps, `P = positiveDataPrefixNorm datum (n+1)` |
| paper-facing | `thm_main_item_iii_executable` (`V158MainItemIII.lean`) | (1) set-driven semantics, (2) conservativeness, (3) Gold with syntactic stabilization, (4) the update bound — all for the same executable learner |

## 4. Cost accounting in the update bound

The analysis is in `updateC_cost_le`. Write `P` for the encoded size of the data seen so far.

| operation | bound used | lemma |
|---|---|---|
| membership, code size | `C ≤ 1400(‖cur‖+1)⁴`, with `‖cur‖ ≤ P` | `constructV116H_codeSize`, `constructV116C_lists_le` |
| membership, names | `Λ ≤ ‖cur‖ ≤ P` | `constructV116H_nameBound` |
| membership, word | `|w|+1 ≤ P+1` | — |
| membership, total | `≤ 21999073608000000 · (P+1)^20` | `codeMemberC_cost_le` |
| duplicate test | `≤ |data|(|w|+2)+1 ≤ 2(P+1)²` | `wordMemC_snd_le` |
| append | `|data|+1` | `appendC_snd` |
| rebuild | `≤ 1400(‖data'‖+1)⁴ ≤ 1400(P+1)⁴` | `constructV116Cost_le`, `inputNorm_newData_le` |
| sizes vs. data seen | `‖data‖ = ‖acc_n‖ ≤ prefix(n)`, `‖cur‖ = ‖K_n‖ ≤ prefix(n)` | existing `concreteAccumulatedSample_norm_le_prefix`, `concreteConservativeHypothesis_norm_le_prefix` |

The degree 20 is not optimized. It comes from:
- the generic Horn engine, quadratic in the chart domain;
- the quartic code-size bound.

The manuscript claims only "polynomial".

## 5. Agreement with the manuscript

* **"Set-driven reconstruction operator `B_h`".** The operator semantics is `BatchLanguage H K`, a function of the set `K`. The executable learner stores samples in arrival order, so two runs with the same sample set may write syntactically different codes for the same `B_h(K)`. **We do not call the written code set-driven.** We prove only that its language is `L(B_h(K_n))`.
* **"Efficiently computable `h`".** Letter-type lookups and monoid operations are unit cost (fixed finite `M`). The learner uses only `h` on letters.
* **"Nonempty `L`".** The theorems assume a positive presentation, which implies nonemptiness.

## 6. Not covered

* RAM / pointer-machine operation count only. No bit complexity, no compiled-code timing.
* The cost of the initial state (writing the code of the empty sample) is outside the per-update bound.
