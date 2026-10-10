# TCS #1 v144 (→ v148) — numbered claims × Lean crosswalk (2026-10-10)

> **Manuscript.** The request targets v144 (`Papers` `68a325e`, `main.tex` sha256 `d9c23a4156ea5713469044a397b3775361786ba731485c4a95ba685d1547b742`). Papers `main` is now at **v148** (`04994e0`, sha256 `824fc84a0e7ba273d014187e95464f5cb015d282f13fed98cdceb85b180a0e7b`). This table is checked against **both**.
> **Lean.** Branch `audit/tcs1-v128-exact-delta` (Draft PR #8). New V144 theorems first verified in CI [#1036](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38042988338) (`315f25a`, all 5 gates). Latest GREEN including the axiom guards: `313aa04c95a16d09ccc5c7ead3d62ae0d1f5a715` — [CI #1040](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38044662069) SUCCESS (all 5 gates, including the V144 `#guard_msgs` axiom audit and the `#guard` execution example).
> **Version check (mechanical; no assumption that v135 = v144).** All three versions have 32 numbered environments (30 claims + 2 definitions) with the same labels in the same order. After whitespace normalisation, compared with v135:
> * **statement changed:** only `prop:linear-separator-example` (v142/v144);
> * **proof changed:** `prop:yl-special` (v138), `prop:li-window` (v139 footnote), `thm:poly-build` (v140/v141), `prop:linear-separator-example` (v142), `prop:nonlinear-rs-example` (v143–v148);
> * v144 → v148: only the `prop:nonlinear-rs-example` proof (Q-examples, direct entry-height definition, canonical completion, removal of the one-letter Q recursion).
> All other statements and proofs are textually identical to v135.

Legend: **F** = manuscript-exact Lean theorem, CI-verified. **R** = reuse of an existing verified Lean theorem. **P** = partially formalized; the remainder is named.

| # | Label | Lean | Grade | Remaining / notes |
|---:|---|---|:---:|---|
| 1 | `prop:regular-auto` | `regular_auto_proposition_package`; `regular_exists_fixedHSubstitutable` | R | — |
| 2 | `prop:finite-info-closure` | (i) `fixedHSubstitutable_inter_product`; (ii) `finiteInfoClosure_ii_cfl` + `regularFilterGrammar_language` (CI #1004); **(iii) `InverseHom.finiteInfoClosure_iii_cfl`, `InverseHom.cfl_inverseImage` (CI #1022)** with RS part `inverseImage_fixedHSubstitutable_with_erasureFlag` | **F** | (iii) now includes the CFL side for possibly erasing `φ` (transducer-refined grammar + insertion of erasing letters + restriction to valid states + finite indexed presentation). No external closure theorem remains for (i)–(iii). |
| 3 | `prop:yl-special` | `fixedWindowSubstitutable_iff_fixedHSubstitutable` | R | v138 changed only the proof (short-word bound $m_0=\max(1,k+\ell)$ made explicit); statement unchanged. |
| 4 | `thm:main` | (i) **`PolyBuild.thm_polyBuild` (CI #1016)** for the v116 `B_h`, plus `sample_consistency`; (ii) `indexedFixedH_exists_characteristic_sample`; (iii) `indexedFixedH_learning_materialized_core`, `corollary_poly_update_materialized`, **`cor_ilt_v116` (CI #1022)**; (iv) `thm_main_item_iv`, `thm_main_item_iv_fixedWindow` (CI #1000), `cor_liThickness_bound_v116` (CI #1004); **(v) `thm_main_item_v`, `thm_main_item_v_bound_v116` (CI #1022)** | **F** | All five items have Lean theorems. (iii)'s per-update time bound is the v79 materialized-learner accounting (membership test by table-backed CYK on the extensionally equal representation); writing each v116 output grammar is separately quartic (`cor_ilt_v116`). |
| 5 | `prop:li-window` | `positiveImageTrivial_iff_exists_positiveWindowKernelRefines`; `positiveImageTrivial_iff_explicitWindowKernelRefines` (window `n=|h(Σ⁺)|+1`); `fixedWindow_positiveImageTrivial`; **`prop_liWindow_classUnion`, `prop_liWindow_classUnion_cfl`** (`V135LiWindowClassUnion.lean`, CI #1008) | **F** | "Locally trivial" is encoded as `PositiveImageSandwichTrivial` (`e·s·e=e` for idempotent `e` and all `s` in `h(Σ⁺)`, with elements represented by nonempty words) — the standard definition, not a separate Lean theorem about Mathlib semigroups. v139 added a proof footnote only; statement unchanged. |
| 6 | `lem:sample-consistency` | `sample_consistency` | R | — |
| 7 | `thm:soundness` | `batchLanguage_sound`; `substringBatchLanguage_eq_batchLanguage` | R | — |
| 8 | `prop:typed-core` | `concreteTypedActive_language_eq_untyped`; `typedDerives_yield_type`; `retainedTypedNonstartLanguage_eq_inter_fiber` | R | — |
| 9 | `thm:complete` | `canonicalWitnessWords_completeness`; `substringBatchLanguage_eq_batchLanguage` | R | — |
| 10 | `thm:reconstruction-fixed-h` | `exact_reconstruction_of_qualitative_reducedness`; `v116TabulatedBatchLanguage_eq_batchLanguage` | R | — |
| 11 | `cor:ilt` | `materializedConservative_gold_identification_explicit`; **`cor_ilt_v116` (CI #1022)** | **F** | The learner whose outputs are the grammar codes written by the v116 constructor: outputs stabilize syntactically, the limit generates the target, each output written within `1400(‖K_n‖+1)^4` steps. Listing `K_n` (`Finset.toList`) is not costed. |
| 12 | `thm:poly-build` | `PolyBuild.thm_polyBuild`, `constructV116Cost_le` (CI #1016) | **F** | Statement unchanged. v141 rewrote the proof: Rule (U) by direct enumeration of (observed factor occurrence $(u,x,v)$, sample word $w$) pairs, $y$ determined by $w=uyv$; no buckets, tries or ID sorting; duplicates not removed; $O(n_K^3)$ candidates × $O(n_K)$ = $O(n_K^4)$. `constructV116C` enumerates (occurrence $w[0:i],w[i:j],w[j:]$) × (sample word $w'$) × end position $j'$, compares contexts letter by letter and does not deduplicate: the same $O(n_K^3)$ iterations × $O(n_K)$ work, proved $\le 1400(\|K\|+1)^4$. The manuscript's cached $h$-values ($O(n_K^2)$ multiplications) are replaced by per-candidate typing, inside the same quartic budget. **The new proof matches the Lean algorithm more closely than v135 did.** |
| 13 | `lem:typed-thickness-bound` | `canonicalWitnessFinset_sampleNorm_le_typedThickness` et al. | R | — |
| 14 | `cor:typed-thickness-data` | `canonicalWitnessFinset_sampleNorm_le_typedThickness`; `indexedFixedH_exists_characteristic_sample` | R | — |
| 15 | `prop:typed-thickness-gap` | `v128_exponential_gap_manuscript_instance` | R | — |
| 16 | `lem:window-typed-yield` | `fixedWindow_reduced_minimal_typed_yield_length_le` | R | — |
| 17 | `thm:window-thick` | `concreteFixedWindowSection7_package`; `classicalFixedWindowSection7_package` | R | — |
| 18 | `prop:thick-ssbnf-normal` | `indexed_proposition74_full_package`; **`SSBNFNorm.prop_thickSSBNFNormal_executable`, `…_executable_degenerate`, `normalizeSSBNF_steps_le` (V144)** | **F** | Executable normalizer `normalizeSSBNF` in the appendix order (front end; ε-elimination after binarization, ≤ 3 variants per binary rule; unit closure; unit elimination; productive and reachable trimming; separated start). Its output is proved to be exactly the existing reduced SSBNF grammar, so the existing size and thickness bounds apply. **Time: ≤ 900·(n+1)^6 steps**, n = `normalizationScale` (cost model in `V144_SSBNF_NORMALIZATION_TIME_AUDIT.md`). |
| 19 | `cor:li-thickness` | **`cor_liThickness_exact`, `cor_liThickness_bound` (CI #1000), `cor_liThickness_bound_v116` (CI #1004)** | **F** | See `V135_LI_THICKNESS_MAIN_IV_EXACT_AUDIT_2026-10-10.md`. |
| 20 | `prop:linear-normal` | `indexedLinear_normalization_*` | R | — |
| 21 | `lem:linear-short` | `minimumCanonicalYield_linear_length_le` | R | — |
| 22 | `thm:linear-poly` | `indexedLinear_characteristic_package` | R | — |
| 23 | `prop:linear-separator-example` | `lpm_proposition86_full_semantic`; **`prop_linearSeparatorExample_existsH` (V144)** | **F** | **Statement changed in v142/v144:** “belongs to $\mathcal C^{lin}_h$ for *some* finite-monoid homomorphism $h$” instead of the explicit four-element $h$. The Lean theorem for the explicit `lpmTyping` gives the witness. The manuscript's new proof route ($L_{all}\cap Q$ with finite-information closure (ii)) differs from Lean's direct proof; both prove the same statement. |
| 24 | `prop:nonlinear-rs-example` | `DeltaStar.nonlinear_rs_example_full` | **P** | Statement unchanged; proof rewritten v143–v148 (admissible entry heights $\mathcal Q(x)$, (⋆), (⋆⋆)). Lean proves CFG generation, nonregularity, nonlinearity, $h_\star$-substitutability and failure of every $(k,\ell)$ by its own proof. **Re-graded R→P in this audit:** the clause “deterministic context-free” is not formalized (Lean has a deterministic membership function but no DPDA model). The v135 table did not record this. |
| 25 | `thm:ctr-non-kl` | `CappedCounter.theorem_ctr_non_kl` | R | — |
| 26 | `lem:finite-monoid-obstruction` | `finiteMonoid_obstruction` | R | — |
| 27 | (unlabelled corollary, uncapped counter) | `UncappedCounter.not_fixedH` | R | — |
| 28 | `cor:dyck-not-rs` | `DyckOne.not_fixedH` | R | — |
| 29 | `lem:rs-fixed-quotient` | `fixedHSubstitutable_fixedRightQuotient` | R | — |
| 30 | `prop:clark-congruential-comparison` | `proposition99_fixedH_inclusion`; `proposition99_dyck_properness` | R | — |

**Unnumbered claim (v134):** introduction example `L={a,aa}`: `V134IntroExample.intro_example_summary` (unchanged).

**Counts (orientation only, not a completion percentage):** F = 8 (#2, #4, #5, #11, #12, #18, #19, #23), R = 21, P = 1 (#24: DCFL clause), B = 0. Total 30. Compared with v135 (F = 6, R = 24): #18 and #23 move to F; #24 moves from R to P because the v144–v148 re-audit found a clause the earlier table had not recorded.

**Not a manuscript change request.** No mathematical error was found in the v144–v148 changes. Two notes:
1. `prop:nonlinear-rs-example`: the DCFL clause is justified by a one-sentence DPDA description in the manuscript. That is standard, but it is not machine-checked.
2. `prop:thick-ssbnf-normal`: the manuscript assumes a *reduced* $G_*$. The Lean normalizer needs no reducedness assumption, and the case of a language contained in $\{\lambda\}$ is handled separately (`…_executable_degenerate`).
