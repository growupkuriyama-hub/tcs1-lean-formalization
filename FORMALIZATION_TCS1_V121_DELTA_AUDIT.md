# TCS #1: theorem-by-theorem v88 → v121 mathematical delta audit

Status: **in progress**. This is an audit, not a declaration of fully verified v121.
The main paper has **since advanced to v123**; this document deliberately freezes
its comparison at the requested **v121** source.

## Exact sources

- v88 theorem-facing Lean archive: `tcs1-v88-formalization-3.0.0`;
  `FORMALIZATION_TCS1_V88.md`.
- v88 exact English paper source: `growupkuriyama-hub/Papers`,
  `01_fixed-h-cfg/main.tex` at
  `00b7d6cb5bf72208ed78b05c21fb2ba8ab88a659`.
- v121 exact English paper source: the same path at
  `f978ae3dbc70ef526d7e99f460d660f3cef7b6b5`.
- The v88 manuscript has **34** theorem/proposition/lemma/corollary
  environments; v121 has **31**. This count **excludes unnumbered
  mathematical statements** and therefore is not by itself a full proof audit.
- Lean work branch `tcs1-v121-reverification` (do not merge to main until CI
  succeeds and all outstanding gaps are resolved or explicitly scoped).

### Classification

- **Inherited**: exact mathematical conclusion already proved at v88; only
  renaming/reformatting or explanatory arguments changed.
- **Bridged**: v121 construction receives an explicit semantic transport
  lemma proved from v88 formalization (subject to a successful Lean CI).
- **Conditional / external**: only the paper-specific consequence is in Lean;
  a mathematically substantial premise is explicitly left as a cited external
  theorem, not advertised as Lean-proved.
- **Partial**: at least one substantive new clause, representation-level
  assertion, or complexity claim is not yet covered by a statement-matching
  formal proof.
- **Open**: no sufficient statement-matching Lean proof presently mapped.

## Exact v121 theorem surface (31 environments)

| # | v121 label / statement | Formalization cross-reference | Audit status |
|---|---|---|---|
| 1 | `prop:regular-auto` — regular recognition and RS | `regular_auto_proposition_package`, `regular_exists_fixedHSubstitutable` | Inherited |
| 2 | `prop:finite-info-closure` — intersection of two RS languages, intersection with regular, erasing inverse-image | `V121FiniteInformationClosure`: `fixedHSubstitutable_inter_product`, `fixedHSubstitutable_inter_recognized_product`, `fixedHSubstitutable_inverseImage` | **Partial**: fixed-h substitutability components proved; CFL closure/background and the exact combined CFL classes are treated externally rather than re-proved |
| 3 | `prop:yl-special` — (k,l) equivalence | `fixedWindowSubstitutable_iff_fixedHSubstitutable` | Inherited |
| 4 | `thm:main` — fixed-h learning five-part theorem | `indexedFixedH_learning_materialized_core`, `corollary_poly_update_materialized`, `indexedFixedWindowSection7_package`, `indexedLinear_characteristic_package`, plus `V121SubstringReconstruction`, `V121LocallyTrivialBridge` | **Partial**: newly generalized local-triviality clause depends on cited algebra theorem; explicit v121 quotient-constructor complexity is not identified with the archived executable construction |
| 5 | `prop:li-window` — local triviality iff finite positive-window kernel refinement, effective (n,n), fixed-window positive images, KL union description | `V121LocallyTrivialBridge.PositiveWindowKernelRefines` and bridge to sample bound | **External/open algebraic core**: the Pin semigroup theorem, sharp (n,n) and reverse inclusion are NOT Lean-formalized here |
| 6 | `lem:sample-consistency` | `sample_consistency`; `substring_sample_consistency` | Bridged |
| 7 | `thm:soundness` | `batchLanguage_sound`; `substring_batchLanguage_sound` | Bridged (v121's original `widehat G` notation) |
| 8 | `prop:typed-core` | `concreteTypedActive_language_eq_untyped`, `typedDerives_yield_type` | Inherited (v121 form); v123 later strengthens this, see below |
| 9 | `thm:complete` | `canonicalWitnessWords_completeness`; `substringBatchLanguage_eq_batchLanguage` | Bridged |
| 10 | `thm:reconstruction-fixed-h` | `exact_reconstruction_of_qualitative_reducedness`; quotient equality | Bridged |
| 11 | `cor:ilt` — Gold identification | `indexedFixedH_concreteGold_identification_nonempty`, `materializedConservative_gold_identification_explicit`; quotient equality | Bridged for generated-language semantics; implementation link remains as item 12 |
| 12 | `thm:poly-build` — explicitly construct v121 substring quotient in polynomial time | `corollary_poly_update_materialized`, archived occurrence/factor-slot bounds | **Partial**: the v121 *new representation and its O(n^4) construction* need a direct program/size/runtime correspondence; extensional equivalence alone is insufficient |
| 13 | `lem:typed-thickness-bound` | `canonicalContext_length_le_of_typedYieldBound`, `canonicalWitnessWords_length_le_typedThickness`, `canonicalWitnessFinset_sampleNorm_le_typedThickness` | Inherited (formatting changed) |
| 14 | `cor:typed-thickness-data` | `canonicalWitnessFinset_sampleNorm_le_typedThickness` and reconstruction package | Inherited |
| 15 | `prop:typed-thickness-gap` — concrete two-element typing h_c, reduced SSBNF of size O(n) and thickness 1, but typed thickness ≥2^n | No matching concrete indexed/typed-gap theorem found in v88 archive | **Open**: genuinely new source-to-typed exponential gap; needs explicit indexed grammar, reducedness, language, trim survival, and shortest typed yield |
| 16 | `lem:window-typed-yield` | `fixedWindow_reduced_minimal_typed_yield_length_le`, `concreteTypedActive_minimalCanonicalWitnessWords_length_le_fixedWindow_v83` | Inherited |
| 17 | `thm:window-thick` | `concreteFixedWindowSection7_package`, `fixedWindowMinimalCanonicalSample_untyped_package` | Inherited |
| 18 | `prop:thick-ssbnf-normal` | `indexed_proposition74_full_package`, `proposition74_thickness_from_yieldBound`, `V121TrimAudit` | Inherited + trim reconnection |
| 19 | `cor:window-transfer` | `indexedFixedWindowSection7_package`, `indexedClassicalFixedWindowSection7_package` | Inherited |
| 20 | `cor:li-thickness` | `characteristicPackage_of_positiveWindowKernelRefinement` | **Conditional/external**: bound proven when a kernel refinement is supplied; sourcing that refinement from locally trivial positive image is the still-external Pin step |
| 21 | `prop:linear-normal` | `indexedLinear_normalization_source_package`, `indexedLinear_normalization_language_eq`, `indexedLinear_normalization_size_le` | Inherited |
| 22 | `lem:linear-short` | `minimumCanonicalYield_linear_length_le` and related witness bound | Inherited |
| 23 | `thm:linear-poly` | `indexedLinear_characteristic_package` | Inherited |
| 24 | `prop:linear-separator-example` | `lpm_proposition86_full_semantic` | Inherited |
| 25 | `prop:nonlinear-rs-example` — Δ* is DCFL, nonregular, nonlinear, RS_h, outside windows | `DeltaStar.nonlinear_rs_example_full` | **Partial**: CFL/grammar, nonregular, nonlinear, RS and non-window parts inherited; **new ‘deterministic’ CFL clause** has parser prose, but no mapped concrete DPDA/DPDA-correctness theorem |
| 26 | `thm:ctr-non-kl` (rho≥2) | `CappedCounter.theorem_ctr_non_kl`; added **unnumbered sharp rho=1** `V121CappedCounterOne.fixedWindowSubstitutable_one` | Inherited for rho≥2; new rho=1 separate CI work |
| 27 | `lem:finite-monoid-obstruction` | `finiteMonoid_obstruction`, `finiteMonoid_obstruction_uniform` | Inherited |
| 28 | unlabeled corollary — uncapped CTR not RS | `UncappedCounter.not_fixedH` | Inherited |
| 29 | `cor:dyck-not-rs` — Dyck1 not RS | `DyckOne.not_fixedH` | Inherited |
| 30 | `lem:rs-fixed-quotient` | `fixedHSubstitutable_fixedRightQuotient` | Inherited |
| 31 | `prop:clark-congruential-comparison` | `proposition99_fixedH_inclusion`, `proposition99_dyck_properness` | Inherited |

### Removed from v121 theorem environment, NOT new verification obligations

Former `prop:ce-special`, `cor:poly-update`,
`lem:fibre-restriction`, `lem:nested-characteristic-obstruction`,
`lem:level-coded-substitutable`, `thm:ordinary-thickness-lower`, and
`prop:ctr-regular` were removed, demoted to prose, or reorganized.
Their Lean evidence is still available in the v88 archive; removing a displayed
environment does **not** invalidate that evidence. In particular, moving the
old lower-bound construction out of the paper avoids a requirement to prove
that lengthy old theorem *again* for v121.

### Important unnumbered edits that raw theorem-environment diffs miss

1. **Trim**: v121 corrects the definition to *nonproductive-first,
   unreachable-second*. The v88 finite normalization already implements
   that order. `V121TrimAudit` explicitly checks language preservation and
   retained productive/reachable claims. The previously incorrect one-shot
   textual trim had NOT been certified as such.
2. **Reconstruction quotient**: v116/v121 states use one `[x]` per **distinct
   observed nonempty factor**, replacing old `[x;u,v]` representatives.
   `V121SubstringReconstruction` proves two-way derivation transport and
   `SubstringBatchLanguage = BatchLanguage`, not only final result equality.
   **However, grammar construction costs for the new representation remain
   separately auditable.**
3. **CTR rho=1**: the sharp (1,1) positive boundary in prose is separate from
   the rho≥2 displayed theorem. Tracked by `V121CappedCounterOne`.
4. **LI algebra / citations**: citation to Pin is **not** automatically a
   Lean-proof of a finite-semigroup classification theorem. The formal
   bridge exposes the precise classical input needed.

## v121 delta files (working branch)

- `LeanCfgProject/TCS1/V121SubstringReconstruction.lean`
- `LeanCfgProject/TCS1/V121FiniteInformationClosure.lean`
- `LeanCfgProject/TCS1/V121TrimAudit.lean`
- `LeanCfgProject/TCS1/V121LocallyTrivialBridge.lean`
- `LeanCfgProject/TCS1/V121CappedCounterOne.lean`

These files are imported by `LeanCfgProject/TCS1/All.lean`. The two workflows
`tcs1-ci.yml` and `v121-fast.yml` build the relevant facade/modules.
Build status must be read from GitHub Actions for the **exact branch SHA**, not
inferred from the existence of source files.

## v122 / v123 later-change addendum (NOT inside v121 claim)

- Current paper source `main.tex` at `f5e5c7a8f3f76836f58537419671f86f269df66a` is **v123** (30 theorem-like environments).
- v122 changes the presentation of soundness/completeness to `\mathcal B_h`
  rather than `\widehat G`, and removes the separately displayed
  fixed-window-transfer corollary (its conclusion remains in theorem/prose).
- v123 **strengthens `prop:typed-core`** from language preservation +
  yield-type invariant to the *retained non-start fibre equality*
  `L_tildeG(A_μ) = L_G(A) ∩ h^-1({μ})`. Its proof obligation is not the
  statement checked by the original v88 facade. An explicit candidate
  proof (`v123_retained_typed_fibre_language_eq`) now lives in the
  separate `tcs1-v123-reverification` branch, pending its own CI.
- The DCFL qualifier for Δ* was already introduced by **v121** relative
  to v88. v123 only standardizes the spelling of “nonlinear”. A concrete
  DPDA correspondence remains an explicit unmapped claim.

## Current outstanding obligations before an honest “v121 verified” claim

1. The five v121 modules **have passed** the dedicated delta build and
   placeholder check at SHA `a8aba31172737fd91a82d61dea95a92b832a42c6`;
   the **full inherited audit/facade CI** must also finish successfully.
2. Verify the concrete **typed-thickness-gap** example, not just a numerical
   bound for abstract typed symbols. The separate v123 branch contains
   `V121TypedGapKernel.lean` for the exact exponential E_i subgrammar yield,
   but this does not yet prove the full source grammar/trim bound.
3. Reconnect the **exact v121 quotient grammar constructor**, including
   enumerator/size and polynomial construction, to Lean's verified executable
   learner (the language-theoretic quotient bridge is already present).
4. Decide and document semigroup/CFL closure literature boundary versus
   internal proof: classical locally trivial equivalence currently external.
5. Explain/classify the Δ* **deterministic** pushdown claim.
6. Independently rerun a full theorem-facing review against the **final**
   version (v123 or later), not a transient manuscript SHA.

### Claim discipline

Do **not** promote `current_verification` to v121, do not mint a v121
Lean DOI or say the v121 manuscript as a whole has a completed theorem-facing
Lean verification while any of the above unproved obligations is unresolved.
An all-green CI would establish correctness of **what is formalized**, not
automatic completeness of coverage.
