# TCS #1 v135 — numbered claims × Lean crosswalk (2026-10-10)

> **Manuscript:** `Papers/01_fixed-h-cfg/main.tex` v135, sha256 `e8590799dbb889f6a375f61c6b9f8c00f3c23d6691d73561808d0989e450ecad` (Papers commit `2e67f3a`).
> **Lean:** branch `audit/tcs1-v128-exact-delta` (Draft PR #8). CI numbers below are the runs that compiled the cited declarations.
> **Version check (done mechanically, not assumed):** v135 has 32 numbered environments — 30 claims + 2 definitions — with the **same labels in the same order as v128**, and every numbered statement and every proof body is **textually identical** to v128 blob `07c53aa9…` after whitespace normalisation. v129–v135 changed only introduction/prior-art prose, the new unnumbered example `L={a,aa}` (v134), the placement of Yoshinaka's `L₀`, one wording change ("needed" → "used in the present completeness proof"), and the bibliography. Hence the v128 correspondences carry over verbatim; only the rows changed by today's proofs are re-graded.

Legend: **F** = manuscript-exact Lean theorem now stated and CI-verified; **R** = established reuse of an existing verified Lean theorem (core content; not every typographical detail re-audited); **B** = bridge still needed; **P** = partially formalized, remainder named.

| # | Label | Lean | Grade | Remaining / notes |
|---:|---|---|:---:|---|
| 1 | `prop:regular-auto` | `regular_auto_proposition_package`; `regular_exists_fixedHSubstitutable` | R | — |
| 2 | `prop:finite-info-closure` | (i) `fixedHSubstitutable_inter_product`; **(ii) `finiteInfoClosure_ii_cfl` + `regularFilterGrammar_language` (CI #1004)**; (iii) RS part `inverseImage_fixedHSubstitutable_with_erasureFlag` | **P** | (ii) now complete *including* the CFL side (explicit finite typed-refinement grammar). Only (iii)'s CFL clause — closure of CFLs under (possibly erasing) inverse homomorphisms — is still the external classical theorem. |
| 3 | `prop:yl-special` | `fixedWindowSubstitutable_iff_fixedHSubstitutable` | R | — |
| 4 | `thm:main` | (i)/(iii) `indexedFixedH_learning_materialized_core`, `corollary_poly_update_materialized`; (ii) `indexedFixedH_exists_characteristic_sample`; **(iv) `thm_main_item_iv`, `thm_main_item_iv_fixedWindow` (CI #1000), `cor_liThickness_bound_v116` (CI #1004)**; (v) `indexedLinear_characteristic_package` | **B** | (iv) is now F. Open: (i) polynomial *construction time* of the v116 tabulated `B_h` itself (the v79 materialized learner's polynomial work bound covers an extensionally equal operator; v116 language equality is CI #858). (v)'s quantifier form was not re-audited this session. |
| 5 | `prop:li-window` | `positiveImageTrivial_iff_exists_positiveWindowKernelRefines`; `positiveImageTrivial_iff_explicitWindowKernelRefines` (window `n=|h(Σ⁺)|+1`); `fixedWindow_positiveImageTrivial`; **`prop_liWindow_classUnion`, `prop_liWindow_classUnion_cfl`** (`V135LiWindowClassUnion.lean`, CI #1008) | **F** | "Locally trivial" is encoded as `PositiveImageSandwichTrivial` (`e·s·e=e` for idempotent `e` and all `s` in `h(Σ⁺)`, with elements represented by nonempty words) — the standard definition, not a separate Lean theorem about Mathlib semigroups. |
| 6 | `lem:sample-consistency` | `sample_consistency` | R | — |
| 7 | `thm:soundness` | `batchLanguage_sound`; `substringBatchLanguage_eq_batchLanguage` | R | — |
| 8 | `prop:typed-core` | `concreteTypedActive_language_eq_untyped`; `typedDerives_yield_type`; `retainedTypedNonstartLanguage_eq_inter_fiber` | R | — |
| 9 | `thm:complete` | `canonicalWitnessWords_completeness`; `substringBatchLanguage_eq_batchLanguage` | R | — |
| 10 | `thm:reconstruction-fixed-h` | `exact_reconstruction_of_qualitative_reducedness`; `v116TabulatedBatchLanguage_eq_batchLanguage` | R | — |
| 11 | `cor:ilt` | `materializedConservative_gold_identification_explicit`; `indexedFixedH_concreteGold_identification_nonempty` | B | Lean learner's hypotheses are `BatchLanguage` samples; v116 language equality makes them extensionally the manuscript's hypotheses, but a learner literally outputting v116 grammars is not packaged. |
| 12 | `thm:poly-build` | v79 `MaterializedProductionCost`; v128 cubic candidate counts; **`v116LiteralOutputLength_le_quartic`, `v116ScanAndWriteBudget_le_quartic`** (`V135SubstringLiteralOutputSize.lean`, CI #1008) | **B** | Output writing of the actual v116 tables is now quartic (non-conditional). Open: canonical-identifier preprocessing and a time model for the v116 constructor (plan in handoff §5). Do not call the quartic *time* bound proved. |
| 13 | `lem:typed-thickness-bound` | `canonicalWitnessFinset_sampleNorm_le_typedThickness` et al. | R | — |
| 14 | `cor:typed-thickness-data` | `canonicalWitnessFinset_sampleNorm_le_typedThickness`; `indexedFixedH_exists_characteristic_sample` | R | — |
| 15 | `prop:typed-thickness-gap` | `v128_exponential_gap_manuscript_instance` | R | — |
| 16 | `lem:window-typed-yield` | `fixedWindow_reduced_minimal_typed_yield_length_le` | R | — |
| 17 | `thm:window-thick` | `concreteFixedWindowSection7_package`; `classicalFixedWindowSection7_package` | R | — |
| 18 | `prop:thick-ssbnf-normal` | `indexed_proposition74_full_package`; `proposition74_thickness_from_yieldBound` | R | Size/thickness/language parts; "in polynomial time" is not a Lean theorem. |
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

**Counts (orientation only, not a completion percentage):** F = 2 (#5, #19), R = 24, B = 3 (#4 — item (iv) itself is F —, #11, #12), P = 1 (#2). Total 30. Previous v128 grading was R=24/B=3/P=1/O=2; both O items (#5, #19) are now closed as CI-verified Lean theorems (last GREEN `d130c3d`, CI #1008).
