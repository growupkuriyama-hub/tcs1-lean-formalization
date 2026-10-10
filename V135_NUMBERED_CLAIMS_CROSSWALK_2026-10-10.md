# TCS #1 v135 — numbered claims × Lean crosswalk (2026-10-10, updated evening)

> **Evening update:** rows #2, #4, #11, #12 upgraded to F with CI #1016/#1022 (latest GREEN `a27fa38`, CI #1024, with axiom guards). Row #18's polynomial-time clause is the only remaining unformalized part of a numbered claim in this table.

> **Manuscript:** `Papers/01_fixed-h-cfg/main.tex` v135, sha256 `e8590799dbb889f6a375f61c6b9f8c00f3c23d6691d73561808d0989e450ecad` (Papers commit `2e67f3a`).
> **Lean:** branch `audit/tcs1-v128-exact-delta` (Draft PR #8). CI numbers below are the runs that compiled the cited declarations.
> **Version check (done mechanically, not assumed):** v135 has 32 numbered environments — 30 claims + 2 definitions — with the **same labels in the same order as v128**, and every numbered statement and every proof body is **textually identical** to v128 blob `07c53aa9…` after whitespace normalisation. v129–v135 changed only introduction/prior-art prose, the new unnumbered example `L={a,aa}` (v134), the placement of Yoshinaka's `L₀`, one wording change ("needed" → "used in the present completeness proof"), and the bibliography. Hence the v128 correspondences carry over verbatim; only the rows changed by today's proofs are re-graded.

Legend: **F** = manuscript-exact Lean theorem now stated and CI-verified; **R** = established reuse of an existing verified Lean theorem (core content; not every typographical detail re-audited); **B** = bridge still needed; **P** = partially formalized, remainder named.

| # | Label | Lean | Grade | Remaining / notes |
|---:|---|---|:---:|---|
| 1 | `prop:regular-auto` | `regular_auto_proposition_package`; `regular_exists_fixedHSubstitutable` | R | — |
| 2 | `prop:finite-info-closure` | (i) `fixedHSubstitutable_inter_product`; (ii) `finiteInfoClosure_ii_cfl` + `regularFilterGrammar_language` (CI #1004); **(iii) `InverseHom.finiteInfoClosure_iii_cfl`, `InverseHom.cfl_inverseImage` (CI #1022)** with RS part `inverseImage_fixedHSubstitutable_with_erasureFlag` | **F** | (iii) now includes the CFL side for possibly erasing `φ` (transducer-refined grammar + insertion of erasing letters + restriction to valid states + finite indexed presentation). No external closure theorem remains for (i)–(iii). |
| 3 | `prop:yl-special` | `fixedWindowSubstitutable_iff_fixedHSubstitutable` | R | — |
| 4 | `thm:main` | (i) **`PolyBuild.thm_polyBuild` (CI #1016)** for the v116 `B_h`, plus `sample_consistency`; (ii) `indexedFixedH_exists_characteristic_sample`; (iii) `indexedFixedH_learning_materialized_core`, `corollary_poly_update_materialized`, **`cor_ilt_v116` (CI #1022)**; (iv) `thm_main_item_iv`, `thm_main_item_iv_fixedWindow` (CI #1000), `cor_liThickness_bound_v116` (CI #1004); **(v) `thm_main_item_v`, `thm_main_item_v_bound_v116` (CI #1022)** | **F** | All five items have Lean theorems. (iii)'s per-update time bound is the v79 materialized-learner accounting (membership test by table-backed CYK on the extensionally equal representation); writing each v116 output grammar is separately quartic (`cor_ilt_v116`). |
| 5 | `prop:li-window` | `positiveImageTrivial_iff_exists_positiveWindowKernelRefines`; `positiveImageTrivial_iff_explicitWindowKernelRefines` (window `n=|h(Σ⁺)|+1`); `fixedWindow_positiveImageTrivial`; **`prop_liWindow_classUnion`, `prop_liWindow_classUnion_cfl`** (`V135LiWindowClassUnion.lean`, CI #1008) | **F** | "Locally trivial" is encoded as `PositiveImageSandwichTrivial` (`e·s·e=e` for idempotent `e` and all `s` in `h(Σ⁺)`, with elements represented by nonempty words) — the standard definition, not a separate Lean theorem about Mathlib semigroups. |
| 6 | `lem:sample-consistency` | `sample_consistency` | R | — |
| 7 | `thm:soundness` | `batchLanguage_sound`; `substringBatchLanguage_eq_batchLanguage` | R | — |
| 8 | `prop:typed-core` | `concreteTypedActive_language_eq_untyped`; `typedDerives_yield_type`; `retainedTypedNonstartLanguage_eq_inter_fiber` | R | — |
| 9 | `thm:complete` | `canonicalWitnessWords_completeness`; `substringBatchLanguage_eq_batchLanguage` | R | — |
| 10 | `thm:reconstruction-fixed-h` | `exact_reconstruction_of_qualitative_reducedness`; `v116TabulatedBatchLanguage_eq_batchLanguage` | R | — |
| 11 | `cor:ilt` | `materializedConservative_gold_identification_explicit`; **`cor_ilt_v116` (CI #1022)** | **F** | The learner whose outputs are the grammar codes written by the v116 constructor: outputs stabilize syntactically, the limit generates the target, each output written within `1400(‖K_n‖+1)^4` steps. Listing `K_n` (`Finset.toList`) is not costed. |
| 12 | `thm:poly-build` | **`PolyBuild.thm_polyBuild`, `constructV116Cost_le` (CI #1016)**; earlier output-size lemmas `v116LiteralOutputLength_le_quartic` | **F** | Executable step-counted constructor; exact (B)/(U)/(L)/(S)/ε rules; language = `BatchLanguage H K`; **≤ 1400·(‖K‖+1)^4 steps** in the explicit cost model (see `V135_POLY_BUILD_COMPLEXITY_AUDIT.md`). Output may repeat productions (no deduplication). |
| 13 | `lem:typed-thickness-bound` | `canonicalWitnessFinset_sampleNorm_le_typedThickness` et al. | R | — |
| 14 | `cor:typed-thickness-data` | `canonicalWitnessFinset_sampleNorm_le_typedThickness`; `indexedFixedH_exists_characteristic_sample` | R | — |
| 15 | `prop:typed-thickness-gap` | `v128_exponential_gap_manuscript_instance` | R | — |
| 16 | `lem:window-typed-yield` | `fixedWindow_reduced_minimal_typed_yield_length_le` | R | — |
| 17 | `thm:window-thick` | `concreteFixedWindowSection7_package`; `classicalFixedWindowSection7_package` | R | — |
| 18 | `prop:thick-ssbnf-normal` | `indexed_proposition74_full_package`; `proposition74_thickness_from_yieldBound` | R | Size/thickness/language parts. **Open:** "converted in polynomial time" (no executable normalizer with step count). |
| 19 | `cor:li-thickness` | **`cor_liThickness_exact`, `cor_liThickness_bound` (CI #1000), `cor_liThickness_bound_v116` (CI #1004)** | **F** | See `V135_LI_THICKNESS_MAIN_IV_EXACT_AUDIT_2026-10-10.md`. |
| 20 | `prop:linear-normal` | `indexedLinear_normalization_*` | R | — |
| 21 | `lem:linear-short` | `minimumCanonicalYield_linear_length_le` | R | — |
| 22 | `thm:linear-poly` | `indexedLinear_characteristic_package` | R | — |
| 23 | `prop:linear-separator-example` | `lpm_proposition86_full_semantic` | R | — |
| 24 | `prop:nonlinear-rs-example` | `DeltaStar.nonlinear_rs_example_full` | R | — |
| 25 | `thm:ctr-non-kl` | `CappedCounter.theorem_ctr_non_kl` | R | — |
| 26 | `lem:finite-monoid-obstruction` | `finiteMonoid_obstruction` | R | — |
| 27 | (unlabelled corollary, uncapped counter) | `UncappedCounter.not_fixedH` | R | — |
| 28 | `cor:dyck-not-rs` | `DyckOne.not_fixedH` | R | — |
| 29 | `lem:rs-fixed-quotient` | `fixedHSubstitutable_fixedRightQuotient` | R | — |
| 30 | `prop:clark-congruential-comparison` | `proposition99_fixedH_inclusion`; `proposition99_dyck_properness` | R | — |

**Unnumbered v134/v135 claim:** Introduction example `L={a,aa}` — `V134IntroExample.intro_example_summary` (CI #1004): generated by `S→a|aa`, not substitutable under the trivial typing, substitutable under the parity typing which separates `a` from `aa`.

**Counts (orientation only, not a completion percentage):** F = 6 (#2, #4, #5, #11, #12, #19), R = 24 (of which #18 still lacks its time clause). B = 0, P = 0. Total 30.
