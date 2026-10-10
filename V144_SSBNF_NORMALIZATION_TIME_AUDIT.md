# TCS #1 v144–v148 — `prop:thick-ssbnf-normal`: executable normalizer and polynomial time (2026-10-10)

> **Manuscript.** `Papers/01_fixed-h-cfg/main.tex`. The request named v144 (sha256 `d9c23a41…`). Papers `main` has since moved to **v148** (`04994e0`, sha256 `824fc84a…`). The statement of `prop:thick-ssbnf-normal` and the appendix `app:thick-ssbnf` are textually identical in v135, v144 and v148 (checked mechanically).
>
> *"There are fixed polynomials q_size and q_thick such that every reduced CFG G\* generating a nonempty language can be converted in polynomial time into an equivalent reduced SSBNF grammar G satisfying |G| ≤ q_size(|G\*|) and τ_G ≤ q_thick(|G\*|, τ_{G\*}+1)."*
>
> **CI.** All files below were first verified in CI [#1036](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38042988338) (`315f25a`, all 5 gates: delta, critical path, `TCS1.All`, sorry grep, axiom grep). `V144AxiomAudit.lean` adds `#guard_msgs` axiom checks (GREEN in `313aa04c95a16d09ccc5c7ead3d62ae0d1f5a715` — [CI #1040](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38044662069) SUCCESS (all 5 gates, including the V144 `#guard_msgs` axiom audit and the `#guard` execution example)); `V144SSBNFExample.lean` runs the compiled normalizer on `S → aSb | ε` with `#guard` (4 nonterminals, 3 terminal rules, 2 binary rules, ε flag, 4313 steps). Files: `V144HornClosure.lean`, `V144SSBNFNormalizer.lean`, `V144SSBNFBridge.lean`, `V144SSBNFFrontEnd.lean`, `V144SSBNFNormalize.lean`.

## 1. What was missing before

The size, thickness and language parts were already proved for the *semantic* normalization (`indexed_proposition74_full_package`: predicate-defined stages on subtypes of a finite support). There was no executable procedure and no operation count. "Converted in polynomial time" was therefore open (crosswalk row #18).

## 2. What is implemented (all executable, no `Finset` operation in the algorithm)

| Stage (appendix order) | Lean | Implementation |
|---|---|---|
| fresh start S₀ | output field `start := some s`, `epsilon` flag | separated start, written as a flag plus the start child, as in `reducedSSBNFStartRule` |
| terminal isolation (wrappers `W_a`) | `V144SSBNFFrontEnd`: `termOfProd`, wrapper states `old (inr a)` | per production, constant work |
| binarization of long right-hand sides | `binOfProd`, `binOfSuffix`, `suffixStatesC` | suffix states are tails of the input RHS (pointers); one pass per RHS |
| non-start ε-elimination **after** binarization | `nullC` (Horn closure), `dropLeftC`, `dropRightC`, `epsUnitC` | binary rule kept, plus ≤ 2 unit variants (≤ 3 variants per binary rule); **no `2^k` subset enumeration** |
| unit closure | `unitClosureC` = one Horn closure per source state | |
| unit elimination | `unitFreeTermC`, `unitFreeBinC` | rules of `y` copied to every unit predecessor `x` |
| productive trimming | `hornC` on `prodRules` | |
| reachable trimming | `prodBinC`, `reachRulesC`, `hornC` | |
| SSBNF output | `outTermC`, `outBinC`, `SSBNFCode` | |

Generic fixed-point engine: `V144HornClosure.hornC` (rounds of "heads of rules whose body is marked", restricted to the domain list; `|dom| + 1` rounds). Correctness `mem_hornC_iff`; cost `hornC_cost_le`.

Paper-facing normalizer: `SSBNFNorm.normalizeSSBNF nts alph prs A : SSBNFCode (FrontEndState N α) α × Nat`.

## 3. Correctness: the executable output *is* the existing semantic grammar

`V144SSBNFBridge` proves, for any code matching a semantic `BinaryNullableGrammar` (`CodeMatches`), that each computed list equals the existing predicate:

| computed | existing definition | lemma |
|---|---|---|
| `null` | `BinaryNullable` | `mem_null_iff` |
| `eunit` | `EpsilonElimUnitRule` | `mem_eunit_iff` |
| `ureach` | `UnitReach (EpsilonElimUnitRule _)` | `mem_ureach_iff` |
| `uterm`, `ubin` | `UnitFreeTerminalRule`, `UnitFreeBinaryRule` | `mem_uterm_iff`, `mem_ubin_iff` |
| `prod` | `∃ w, UnitFreeDerives _ A w` | `trace_prod_iff` |
| `reach` | `ProductiveUnitFreeReachable` | `trace_reach_iff` |
| output | `reducedSSBNFTerminalRule/BinaryRule/StartRule` | `out_nonterminal_iff`, `out_terminal_iff`, `out_binary_iff`, `out_start_eq`, `out_epsilon_iff` |
| derivations | `UntypedDerives` of the reduced grammar | `codeDerives_iff`, `codeStartLanguage_eq` |

`V144SSBNFNormalize.codeMatches_indexed`: for complete listings of an `IndexedMixedCFG`, the front end writes exactly `indexedFiniteFrontEndGrammar G` (states = the existing support `indexedClosedFrontSupport G`; rules = `frontEndBinaryGrammar` rules, characterized in `frontEnd_terminal_iff`, `frontEnd_binary_iff`, `frontEnd_unit_iff`, `frontEnd_epsilon_iff`).

Hence the existing size, thickness and language theorems apply verbatim to the written output.

## 4. Cost model

Same as `V135CostedPrimitives` (values and step counts produced by the same recursion):

* one step per list cell visited or created and per loop iteration;
* one step per comparison of two source symbols (nonterminal or letter indices; word-RAM unit cost, as for loop indices in `V135`);
* front-end states are compared by `stateEqC`: `old`/`old` in one step, `suffix`/`suffix` **cell by cell** (`PolyBuild.eqC`), so a state comparison costs at most `inputScale + 1`;
* a suffix state is a pointer to a tail of the input right-hand side (sharing, no copy); building one constant-size rule record costs 2–5 steps;
* no `Finset` operation, hashing or sorting is executed. `Finset` appears only in proofs (the round bound of the Horn engine, the support of the existing semantic grammar).

Input: explicit lists `nts`, `alph`, `prs` (`Listing G`: duplicate-free complete listings; `prs` = `(lhs p, rhs p)` for every listed production). `inputScale = |nts| + |alph| + |prs| + Σ|rhs|`; `inputScale_eq_normalizationScale` shows it equals `G.normalizationScale`.

## 5. Proved operation counts

Let `m` bound every list of the front-end code and `E` bound one state comparison.

| stage | bound | lemma |
|---|---|---|
| Horn closure (generic) | `8 (|dom|+1)² (|rules| + Σ|body| + 1) (E+1)` | `hornC_cost_le` |
| front end | `60 (inputScale + 1)` | `frontCodeC_snd_le` |
| nullable | `63 (m+1)³ (E+1)` | `cost_null` |
| ε-elimination | `14 (m+1)² (E+1)` | `cost_eps` |
| unit closure | `134 (m+1)⁴ (E+1)` | `cost_unitClosure` |
| unit elimination | `10 (m+1)³ (E+1)` each | `cost_unitFreeTerm`, `cost_unitFreeBin` |
| productive | `12 (m+1)³ (E+1)` + `32 (m+1)⁵ (E+1)` | `cost_prodRules`, `cost_prod` |
| reachable | `9 (m+1)⁴ (E+1)` + `13 (m+1)³ (E+1)` + `32 (m+1)⁵ (E+1)` | `cost_prodBin`, `cost_reachRules`, `cost_reach` |
| output | `5 (m+1)⁴ (E+1)` each, flags `4 (m+1)(E+1)` | `cost_outTerm`, `cost_outBin`, `cost_flags` |
| **normalizer after front end** | **`400 (m+1)⁵ (E+1)`** | `normalizeTrace_steps_le` |
| **whole normalizer** | **`900 (n+1)⁶`**, `n = G.normalizationScale` | `normalizeSSBNF_steps_le` |

Intermediate sizes (proved): `|null|, |prod|, |reach| ≤ m`; `|eunit| ≤ 3m`; `|ureach| ≤ m²`; `|uterm|, |ubin|, |pbin| ≤ m³`.

## 6. Paper-facing theorems

* `SSBNFNorm.prop_thickSSBNFNormal_executable` (start nonterminal `A` with a nonempty word, source thickness `τR`, `0 < n`): the written grammar
  1. generates exactly `L(G, A)` (`UntypedStartLanguage` of the written code, with its ε flag);
  2. has exactly the nonterminals, terminal rules and binary rules of the reduced SSBNF grammar `Nf` of `indexed_proposition74_full_package`, and start child `old (inl A)`;
  3. has at most `indexedSSBNFGrammarSizeEnvelope n` distinct nonterminals, terminal rules and binary rules; written lists have length `≤ n`, `≤ n³`, `≤ n³`;
  4. every written nonterminal is reachable in the written grammar (`CodeReachable`) and derives a word of length `≤ ssbnfThicknessEnvelope 1 1 n τR = 1 + n² · thicknessBar τR`;
  5. is produced in at most `900 · (n + 1)^6` steps.
* `SSBNFNorm.prop_thickSSBNFNormal_executable_degenerate`: if `A` has no nonempty word, the normalizer writes no nonterminal, rule or start child, and the written grammar (ε flag only) still generates exactly `L(G, A)`. With the previous theorem, the executable normalizer is correct on every input.

## 7. Agreement with the manuscript, and differences

* The statement's "polynomial time" is proved in the cost model of §4. The polynomial is `900 (n+1)^6`; the manuscript gives no explicit degree.
* The appendix says the unit-closure copies `O(n²)` rules. Our written lists may contain repeated rules (no deduplication), with length up to `n³`. The number of *distinct* rules is bounded by the existing envelope. The time bound accounts for the repetitions.
* The input is assumed to be given by explicit lists. The manuscript's `|G*|` corresponds to `G.normalizationScale` (`|N| + |Σ| + |P| + Σ|rhs|`).
* The manuscript assumes `G*` is reduced. Lean does not need this: any finite CFG and any start nonterminal are accepted, and the nonempty-word case and the degenerate case are both covered.
* The manuscript's alphabet `Σ` may be larger than the letters used. Wrapper states `old (inr a)` exist for all listed letters, as in the existing semantic front end, and unused wrappers are trimmed.

## 8. Not covered

* RAM/pointer-machine operation count only. Not compiled-code running time, not bit complexity. Unit cost for comparing two nonterminal or letter indices.
* Cost of producing the input lists from a `Fintype` presentation is outside the algorithm (input format). No `Finset.toList` is used by the normalizer.
* Degree 6 is not optimized. The manuscript does not state a degree.
