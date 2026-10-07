# TCS #1 v121 — theorem-facing crosswalk (working, not a proof certificate)

**Observed 2026-10-07.** Manuscript source: `growupkuriyama-hub/Papers/01_fixed-h-cfg/main.tex`. Authoritative English **v121** SHA-256: `70107ff6ee9c38c84f36cc13cfd741c20722561ec711eea69198d0cd63ab17b6`. The Japanese document is still **v120**; do not assert EN/JP equivalence. The manuscript is a **TCS major revision** in progress.

## Important scope

- **31 actual theorem/proposition/lemma/corollary environments** (30 labeled, one unlabeled uncapped-counter corollary). The existing `V115TheoremSurfaceAudit.lean` crosswalk enumerates **30 v115 environments** and pre-dates the inserted typed-thickness-gap Proposition.
- A Lean `#check`, theorem name, or CI green result means the displayed *Lean statement* type-checked. It does **not** by itself certify all prose, complexity assertions or formal claims in the newest manuscript.
- `prop:li-window` is a classical locally-trivial semigroup result, now correctly attributed to Pin and other semigroup references in v121. Its direct proof and typed-thickness transfer have Lean versions but are **not claimed as novel**.
- EHY Definition 2.8 set-driven polynomial data bound is **not** the Definition 2.5 incremental time-and-data criterion; the latter claim was explicitly withdrawn from the TCS response.

## v121 claim ledger

| # | Source environment | Current Lean bridge / remaining qualification |
|---:|---|---|
| 1 | `prop:regular-auto` | `regular_auto_proposition_package` |
| 2 | `prop:finite-info-closure` | Fixed-h product and recognized filtering proven; **arbitrary erasing inverse-preimage as a concrete CFG** remains open |
| 3 | `prop:yl-special` | `fixedWindowSubstitutable_iff_fixedHSubstitutable` |
| 4 | `thm:main` | Learning semantics and components available; **exact full conjunction, complexity and output** still open |
| 5 | `prop:li-window` | `v115_positiveImageLocallyTrivial_window_refines`, `v118_locallyTrivial_boundary_erasure`; classical provenance in v121 |
| 6 | `lem:sample-consistency` | `sample_consistency` |
| 7 | `thm:soundness` | `batchLanguage_sound` |
| 8 | `prop:typed-core` | `concreteTypedActive_language_eq_untyped`, `typedDerives_yield_type` |
| 9 | `thm:complete` | `canonicalWitnessWords_completeness` |
| 10 | `thm:reconstruction-fixed-h` | `exact_reconstruction_of_qualitative_reducedness` |
| 11 | `cor:ilt` | `indexedFixedH_concreteGold_identification_nonempty` |
| 12 | `thm:poly-build` | Old executable polynomial build compiled, but v116-v121 **exact `O(n_K^4)`** requires a separate proof (older `O(n_K^5)` envelope is insufficient) |
| 13 | `lem:typed-thickness-bound` | `canonicalWitnessFinset_sampleNorm_le_typedThickness` |
| 14 | `cor:typed-thickness-data` | Typed-thickness witness bound and reduced typed language bridge |
| 15 | `prop:typed-thickness-gap` | **Source-exact finite family** and exponential typed `(E_n,1)` witness compiled in `v119Gap_source_to_typed_certificate` (latest full CI at `963aba8` green); `2n+7` production index, n+3 non-start states, ordinary thickness-one/reducedness evidence; avoid claiming any algorithm-independent sample lower bound |
| 16 | `lem:window-typed-yield` | `fixedWindow_reduced_minimal_typed_yield_length_le` |
| 17 | `thm:window-thick` | `concreteFixedWindowSection7_package` |
| 18 | `prop:thick-ssbnf-normal` | `indexed_proposition74_full_package`; v121 trim-order wording to be cross-checked against implementation |
| 19 | `cor:window-transfer` | `indexedFixedWindowSection7_package` |
| 20 | `cor:li-thickness` | `v115_indexedLocallyTrivial_characteristic_package` |
| 21 | `prop:linear-normal` | `indexedLinear_normalization_source_package` and finite-size construction |
| 22 | `lem:linear-short` | `minimumCanonicalYield_linear_length_le` |
| 23 | `thm:linear-poly` | `indexedLinear_characteristic_package`; regular-filter closure of linear targets uses the v121 productive DFA-product bridge, **pending CI** |
| 24 | `prop:linear-separator-example` | `lpm_proposition86_full_semantic`; v121 regular-filter explanation not equivalent to the direct four-element typing witness |
| 25 | `prop:nonlinear-rs-example` | `DeltaStar.nonlinear_rs_example_full` and DPDA component; ensure source conjunction is exact |
| 26 | `thm:ctr-non-kl` | `CappedCounter.theorem_ctr_non_kl`; **v121 wording is only `rho >= 2`**, with `CTR_1` identified as `(1,1)`-substitutable |
| 27 | `lem:finite-monoid-obstruction` | `finiteMonoid_obstruction` |
| 28 | **unnamed** corollary: uncapped counter outside RS | `UncappedCounter.not_fixedH` |
| 29 | `cor:dyck-not-rs` | `DyckOne.not_fixedH` |
| 30 | `lem:rs-fixed-quotient` | `fixedHSubstitutable_fixedRightQuotient` |
| 31 | `prop:clark-congruential-comparison` | `proposition99_fixedH_inclusion`, `proposition99_dyck_properness` |

## Current priority (not yet certified as one theorem)

1. **Finite-state regular filtering of linear CFGs.** `V118LinearFilterShapeBridge` checks three structural ingredients. `V121ProductiveLinearFilter` defines a finite *productive* product-state subtype, explicitly preserving start-language and the full linear-spine wrapper condition. The subsequent arbitrary-indexed-linear and fixed-h-product packages must be compiled before claiming v121's full `C_lin` closure implication.
2. **`O(n_K^4)` for the actual substring-indexed batch grammar.** Existing v116 equivalence is about generated language, not exact construction-time bound.
3. **Concrete CFG for an arbitrary erasing inverse homomorphic preimage.** Substitutability under pulled-back typing is separately machine-checked.
4. **Exact `thm:main` statement and all 31 source claims**, especially output/timing and representation-specific hypotheses.

The immutable archival baseline remains **v88**, tag `tcs1-v88-formalization-3.0.0`, DOI `10.5281/zenodo.23120560`. No v121 archive has been minted. Neither reviewer response nor v121 manuscript was modified in this Lean work.
