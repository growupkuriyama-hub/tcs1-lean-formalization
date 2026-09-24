# TCS #1 v79 Lean coverage report

This report records the paper-facing Lean coverage of the current working
manuscript

- title: *Distributional Learning of Context-Free Languages under Fixed
  Finite-Monoid Typing*;
- manuscript baseline: v79;
- local source audited:
  `TCS-D-26-00494_major_revision_working_v79(1)(1).tex`;
- source SHA-256:
  `3d54aaea1c945e4b9bbdabe92a88f229096d94c93fa3045a3bfda5dfd22426d2`.

The report is deliberately conservative.  It separates four categories:

1. **Lean-internal** — a theorem/definition in the repository discharges the
   mathematical claim;
2. **Definition/convention** — manuscript setup represented by Lean
   definitions, but not a substantive theorem;
3. **Literature/background** — a fact explicitly imported from the literature
   or used only for positioning;
4. **Open/out of scope** — stated as open in the manuscript, or below the
   manuscript's abstraction level (for example machine-code cost semantics).

The compile-time audit facades are:

- `V79PreliminariesAudit.lean`;
- `V79ManuscriptClaimAudit.lean`;
- `V79FrontBackAppendixAudit.lean`;
- `V79FullManuscriptAudit.lean`.

The full facade `LeanCfgProject/TCS1/All.lean` imports all four.

---

## 1. Abstract and Introduction

### Main fixed-h learning claim — Lean-internal

Manuscript source lines 31--34 and 103--107 summarize finite positive
witnesses, exact reconstruction, conservative Gold learning, and polynomial
updates.

Lean cross-references:

- `indexedFixedH_exists_characteristic_sample`;
- `exact_reconstruction_of_qualitative_reducedness`;
- `indexedFixedH_learning_materialized_core`;
- `materializedConservative_gold_identification_explicit`;
- `corollary_poly_update_materialized`.

The Section 6 implementation layer is stronger than the prose summary: the
repository contains a computable factor-slot parser, explicit finite
production tables, a table-backed conservative learner, and explicit
polynomial finite-scan/comparison envelopes.

### Fixed-window and linear characteristic-data claims — Lean-internal

Manuscript lines 34 and 109--115 are covered by:

- `fixedWindowSubstitutable_iff_fixedHSubstitutable`;
- `fixedWindowSubstitutable_zero_iff_fixedHSubstitutable`;
- `indexed_proposition74_full_package`;
- `indexedClassicalFixedWindowSection7_package`;
- `indexedLinear_normalization_source_package`;
- `indexedLinear_characteristic_package`.

The historical phrase that this recovers the "same ... scale established by
Yoshinaka" is a comparison with the cited literature.  Lean verifies the
paper's own bounds and transfer package; it does not formalize Yoshinaka's
paper as an external theorem library.

The broader statement that the union class `RS` (and `RS ∩ CFL`) is not
identifiable from positive data because it is superfinite has a mixed status.
The internal bridge
`regular_exists_fixedHSubstitutable` now states directly that every regular
language belongs to some fixed-h substitutable class, exactly the existential
step needed for the union-class discussion.  Gold's general superfinite
negative theorem, and the standard background fact that every finite language
is regular, remain cited/external rather than being re-proved here.

### Expressiveness claims — Lean-internal

Manuscript lines 117--124 are covered by:

- `CappedCounter.regular_fixedH_outside_every_fixedWindow`;
- `lpm_proposition86_full_semantic`;
- `DeltaStar.nonlinear_rs_example_full`;
- `DyckOne.not_fixedH`;
- `proposition99_fixedH_inclusion`;
- `proposition99_dyck_properness`.

### Background/positioning — literature/background

The Gold impossibility theorem, prior Clark--Eyraud/Yoshinaka/Kanazawa
results, automata-inference typing/domain-bias comparison, and Takada
control-set discussion in lines 43--55 and 84--96 are literature/background
claims, not re-proved by this development.

The manuscript explicitly says that no class separation from the full
control-set framework is claimed.

---

## 2. Preliminaries

### Definitions and conventions — represented internally

The terminal distribution/shared-context layer is represented by:

- `Distribution`;
- `HaveSharedContext`;
- `sharedContext_iff_distribution_inter_nonempty`.

CFG derivation semantics are represented by:

- `MixedDerives`;
- `MixedSymbolsDerive`;
- `MixedNonterminalLanguage`;
- `LeastClosedLanguage`.

Fixed-h substitutability is represented by:

- `FixedFiniteMonoidHom`;
- `FixedHSubstitutable`.

The positive-data sample norm is represented by:

- `reconstructionSampleNorm`;
- `reconstructionSample_card_le_norm`.

The conservative keep/rebuild learner is represented by:

- `concreteAccumulatedSample`;
- `concreteConservativeHypothesis_keep`;
- `concreteConservativeHypothesis_rebuild`.

Empty and epsilon-only endpoints are represented by:

- `batchLanguage_empty_eq`;
- `batchLanguage_singleton_epsilon_eq`;
- `singletonEpsilon_fixedHSubstitutable`;
- `singletonEpsilon_concreteGold_identification`.

### Linear evaluation of the fixed homomorphism — Lean-internal

The manuscript states at lines 222--226 that, after fixing the finite monoid
multiplication table and letter images, `h(w)` is computable by a linear
scan.

This is formalized by:

- `fixedHomLetterProduct`;
- `fixedHomLetterProduct_eq_h`;
- `fixedHomMultiplicationCount`;
- `fixedHomMultiplicationCount_eq_length`;
- `fixedHom_linear_scan_certificate`.

The certified evaluator performs exactly one monoid multiplication per input
symbol.  This is finite-table/combinatorial accounting, not a machine-code
runtime theorem.

### Reasonable encoding convention — convention, not formal theorem

The sentence at lines 180--183 that reasonable CFG encodings are
polynomially equivalent to ordinary production-symbol count is treated as a
representation convention.  The repository proves explicit state/rule/symbol
count bounds once an encoding scale is fixed; it does not formalize a general
metatheorem about all reasonable byte encodings.

---

## 3. Section 3 — Fixed Recognizable Substitutability

All numbered mathematical claims are compile-checked.

| Manuscript claim | Lean cross-reference |
| --- | --- |
| Proposition 3.1, regular recognition / regular languages in RS | `regular_auto_proposition_package`, `regular_exists_fixedHSubstitutable` |
| Proposition 3.2, Clark--Eyraud special case | `clarkEyraud_special_case` |
| Proposition 3.3, exact fixed-window equivalence | `fixedWindowSubstitutable_iff_fixedHSubstitutable` |
| Theorem 3.4, fixed-h learning theorem | `indexedFixedH_learning_materialized_core`, `corollary_poly_update_materialized`, Section 7/8 packages |

Important unnumbered prose is also formalized:

- the post-Theorem 3.4 compatibility paragraph with Gold's superfinite
  obstruction:
  `goldThreeWordSample_not_fixedH` and
  `fixedH_omits_some_finite_language`;
- refinement monotonicity:
  `fixedHSubstitutable_of_refinement`;
- sufficient syntactic-refinement criterion:
  `fixedHSubstitutable_of_type_implies_distribution_eq`;
- strictness of that sufficient criterion:
  `isRegular_of_fixedH_type_refines_distribution`,
  `nonregular_has_same_type_distinct_distribution`, and
  `lpm_fixedH_without_syntactic_kernel_refinement`; the last theorem uses
  the already verified nonregular linear separator to show that fixed-h
  substitutability does not require the finite h-kernel to refine full
  syntactic congruence;
- product typing and kernel intersection:
  `productFixedFiniteMonoidHom_eq_iff`;
- pointwise class-union consequence
  `RS_H ∪ RS_G ⊆ RS_{H×G}`:
  `fixedHSubstitutable_product_of_either`;
- fixed-window counterexample criterion:
  `not_fixedWindowSubstitutable_of_bad_pair`;
- the `(0,0)` endpoint:
  `fixedWindowSubstitutable_zero_iff_fixedHSubstitutable`.

---

## 4. Sections 4--5 — Reconstruction, completeness, and Gold convergence

| Manuscript claim | Lean cross-reference |
| --- | --- |
| Lemma 4.1, sample consistency | `sample_consistency` |
| Theorem 4.2, soundness | `batchLanguage_sound` |
| Proposition 5.1, typed lifting/yield invariant | `concreteTypedActive_language_eq_untyped`, `typedDerives_yield_type` |
| Theorem 5.2, finite-witness completeness | `canonicalWitnessWords_completeness` |
| Theorem 5.3, exact reconstruction | `exact_reconstruction_of_qualitative_reducedness` |
| Corollary 5.4, Gold identification | `indexedFixedH_concreteGold_identification_nonempty`, `materializedConservative_gold_identification_explicit` |

The executable and materialized learners are proved pointwise identical to
the semantic learner used in the Gold proof.

The unnumbered Section 4 motivation that raw batch recomputation need not
stabilize syntactically is also represented at the executable syntax level:
`reconstructionFactorSlotCount_insert` and
`reconstructionFactorSlot_card_lt_insert` show that every genuinely new
sample word strictly enlarges the occurrence-indexed factor/context state
universe.

The unnumbered canonical-witness setup used in Theorem 5.2 is also checked
explicitly:

- `canonicalWitnessWords_subset_target` proves positivity of the canonical
  witness words;
- `canonicalWitnessWords_finite` proves finiteness;
- `indexedReducedSSBNF_untypedStartLanguage_eq_source` connects the
  normalized productive branch back to the source language.

---

## 5. Section 6 — reconstruction/update complexity

### Theorem 6.1 — Lean-internal

The finite reconstruction space and output bounds are covered by:

- `reconstructionFactorSlotCount_le_sq`;
- `reconstructionSplitSlotCount_le_cube`;
- `reconstructionFactorPairCount_le_fourth`;
- `reconstructionRuleCandidateSpace_card_le_fourth`;
- `reconstructionOutputEncodingEnvelope_le_degreeFive`;
- `concreteAccumulated_directCandidateScan_le_prefix_degreeFive`.

### Corollary 6.2 — Lean-internal

The strongest current update package is:

- `reconstructionProductionTableScanEnvelope_polynomial_form`;
- `materializedConservative_productionCard_le_prefix`;
- `materializedConservative_update_work_le_prefix`;
- `conservativeMaterializedUpdateWorkEnvelope_polynomial_form`;
- `corollary_poly_update_materialized`.

This includes production-table materialization, all-source finite unit
closure, CYK membership work, and a possible rebuild.

### Grammar-size-only characteristic-data obstruction — Lean-internal

The unnumbered Section 6 paragraph showing why arbitrary CFG size alone
cannot polynomially bound positive characteristic data is fully represented
by the doubling family:

- `singleton_fixedHSubstitutable`;
- `singleton_characteristic_sample_contains`;
- `singleton_doubling_characteristic_norm_ge`;
- `doublingGrammarEncodingScale_eq`;
- `doublingStartLanguage_eq_singleton`;
- `grammarSizeOnlyDataBound_obstruction`.

The formal package exhibits a grammar encoding scale `4*n + 6`, language
`{a^(2^n)}`, fixed-h substitutability for every fixed finite typing, and a
characteristic-sample norm lower bound `2^n + 1`.

### Cost-model boundary — explicit limitation

The cost theorems count finite scans, candidate comparisons, production-table
entries, and reconstruction output.  They do not formalize Lean evaluator
steps, allocation costs, hash-table behavior, or generated machine code.

---

## 6. Section 7 — fixed-window thick data

| Manuscript claim | Lean cross-reference |
| --- | --- |
| Lemma 7.1, bounded fixed-window typed yields | `fixedWindow_reduced_minimal_typed_yield_length_le` |
| Lemma 7.2, bounded contexts/witnesses | `exists_fixedWindow_reduced_short_reaching_context`, `canonicalWitnessWords_length_le_fixedWindow_of_structural_reachability` |
| Theorem 7.3, polynomial thick data | `concreteFixedWindowSection7_package`, `classicalFixedWindowSection7_package` |
| Proposition 7.4, thickness-preserving SSBNF normalization | `indexed_proposition74_full_package`, `proposition74_thickness_from_yieldBound` |
| Corollary 7.5, fixed-window transfer | `indexedFixedWindowSection7_package`, `indexedClassicalFixedWindowSection7_package`, `indexedZeroWindowSection7_package` |

The appendix proof infrastructure is also checked directly:

- `exists_fixedWindow_cycle_shortened_kernel_ranked`;
- `exists_fixedWindow_long_typed_yield`;
- `exists_fixedWindow_bounded_typed_yield`;
- `activeTyped_productive_bounded_yield`;
- `canonicalYieldContextBounds_fixedWindow_of_structural_reachability`.

The normalization appendix is covered by exact language-preservation and size
theorems for terminal isolation, binarization, epsilon elimination, unit
elimination, productive/reachable trimming, and separated-start conversion.

---

## 7. Section 8 — linear subclass

| Manuscript claim | Lean cross-reference |
| --- | --- |
| Proposition 8.1, linear-spine SSBNF normalization | `indexedLinear_normalization_source_package`, `indexedLinear_normalization_language_eq`, `indexedLinear_normalization_shape`, `indexedLinear_normalization_size_le` |
| Lemma 8.2, short canonical witnesses | `minimumCanonicalYield_linear_length_le`, `minimumCanonicalContext_linear_length_le`, `mem_canonicalWitnessFinset_linear_length_le` |
| Theorem 8.3, polynomial characteristic data | `indexedLinear_characteristic_package` |
| Proposition 8.4, nonregular linear separator | `lpm_proposition86_full_semantic` |

The classical characterization of linear languages by one-turn pushdown
automata, cited in the manuscript for background, is classified as
**literature/background** rather than re-proved in the Lean artifact.

Appendix-level construction and witness proofs are additionally checked by:

- `indexedLinear_rawPreprocessedLanguage_eq_source`;
- `preparedLinear_normalization_package`;
- `indexedLinear_reduced_normalization_semantic_package`;
- `normalize_linearYieldSpine_to_nodup`;
- `exists_linear_short_yield`;
- `linearReachingSpine_short_context`;
- `linearCanonicalContext_length_le_twice_card`;
- `canonicalWitnessFinset_linear_norm_le`.

---

## 8. Section 9 — expressiveness and boundaries

| Manuscript claim | Lean cross-reference |
| --- | --- |
| Proposition 9.1, nonlinear fixed-h Delta-star target | `DeltaStar.nonlinear_rs_example_full` |
| Proposition 9.2, capped counter regularity | `CappedCounter.proposition_ctr_regular` |
| Theorem 9.3, capped counter outside all fixed windows | `CappedCounter.theorem_ctr_non_kl` |
| Corollary 9.4, regular strict separation KL ⊊ RS | `CappedCounter.regular_fixedH_outside_every_fixedWindow` plus exact fixed-window equivalence |
| Lemma 9.5, finite-monoid obstruction | `finiteMonoid_obstruction`, `finiteMonoid_obstruction_uniform` |
| Corollary 9.6, uncapped counter outside RS | `UncappedCounter.not_fixedH` |
| Corollary 9.7, one-bracket Dyck outside RS | `DyckOne.not_fixedH` |
| Lemma 9.8, fixed-word quotient | `fixedHSubstitutable_fixedRightQuotient` |
| Proposition 9.9, Clark congruential comparison | `proposition99_fixedH_inclusion`, `proposition99_dyck_properness` |

The Delta-star development is stronger than the manuscript proof at one
point: the Lean repository proves its own bounded linear pumping obstruction
and internal Double-Delta nonlinearity theorem, rather than depending on the
classical cited nonlinearity fact.

### Literature/background statements in Section 9

The following are not separate internal proof obligations in the current
artifact and are classified as **literature/background**:

- that the uncapped counter language is deterministic context-free via the
  displayed/standard DPDA construction;
- that the one-bracket Dyck language is a standard deterministic
  context-free language;
- that the Lukasiewicz language is standard deterministic context-free and
  has the cited classical identity under the chosen coding.

The Lean development formalizes the RS obstructions and quotient argument
that are original proof dependencies of the paper.

---

## 9. Conclusion

The positive summary statements in manuscript lines 1478--1491 are covered by
the Section 3--9 theorem packages above.

The following lines are intentionally **open**, not missing proof obligations:

- complete characterization of `RS ∩ CFL`;
- criteria for useful finite typings;
- unknown-h learning;
- extensions to richer grammar formalisms;
- whether arbitrary fixed-h general CFGs admit characteristic-data bounds
  polynomial in grammar size and thickness.

No Lean theorem is asserted for these open questions.

---

## 10. Final coverage status

At the manuscript abstraction level, the current v79 branch has explicit
Lean coverage for:

- the theorem-bearing Preliminaries claims;
- every numbered theorem, lemma, proposition, and corollary in Sections 3--9;
- the main mathematical claims repeated in the Abstract, Introduction, and
  Conclusion;
- the fixed-window normalization/witness appendices;
- the linear normalization/witness appendices;
- important unnumbered Section 3 refinement/product-typing claims;
- the Section 3 syntactic-kernel strictness paragraph;
- the Section 6 grammar-size-only data lower-bound example;
- executable membership and conservative learning;
- explicit finite production-table materialization and polynomial
  combinatorial update accounting.

The remaining non-internal material falls into one of three stated
categories: literature/background, representation convention, or explicit
open problem.  No currently known paper-facing mathematical gap remains in
the v79 theorem surface.

The strongest integration checkpoint is
`V79FullManuscriptAudit.lean`, imported by `TCS1.All`.
