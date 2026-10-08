# TCS #1 v128 — exact-version Lean delta audit (IN PROGRESS)

> **2026-10-09 最新の引継ぎ正本:** [`START_HERE_TCS1_V128.md`](./START_HERE_TCS1_V128.md)。追跡 [Issue #9](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/issues/9)。最新の検証済み Lean code CI は **#901 SUCCESS**（run `37846653643`、crosswalk code commit `9605407f`）。直近の新しい数学的証明を追加した checkpoint は **#890**（run `37830187537`、`e7858324`）、ただし文書追記後の HEAD と CI の一致は再確認すること。旧版の学習器を作り直さない。

Date: 2026-10-08. Manuscript source of truth: `growupkuriyama-hub/Papers/01_fixed-h-cfg/main.tex`.
Manuscript internal version: **v128**, SHA-256 recorded in PAPER.yaml:
`cb18358871d34f6120fed03bc9da7bfed5f1f3095487cca03b07d40ae4d90128`.
Historical verified Lean baseline: **v88** (`tcs1-v88-formalization-3.0.0`).

## Scope and honesty rule

**This is NOT a completed exact-version v128 manuscript verification.** The v88
archive remains the only completed exact synchronization. Do not replace the
`current_verification: v88` metadata or claim that all v128 results are
machine-checked until the obligations below have proofs and passing CI.

## Source surface comparison

The v88 English manuscript has 34 theorem/proposition/lemma/corollary
environments; v128 has 30. Added labeled statements:

- `prop:finite-info-closure` — intersections with product typing, regular
  filtering, and erasing inverse homomorphism with an added empty-image flag.
- `prop:li-window` — locally trivial positive image semigroups and fixed-window
  kernel refinement; original prior-art attribution must be retained.
- `prop:typed-thickness-gap` — exponential typed-thickness gap at ordinary
  thickness one for fixed two-element typing.
- `cor:li-thickness` — characteristic-data bound under locally trivial typing.

Removed labeled environments include `prop:ce-special`,
`prop:ctr-regular`, `thm:ordinary-thickness-lower`,
`lem:fibre-restriction`, `lem:nested-characteristic-obstruction`,
`lem:level-coded-substitutable`, `cor:poly-update`, and
`cor:window-transfer`. Removal is **not** mathematical refutation;
historical Lean proofs remain available.

Changed labeled statements include:
`prop:typed-core`, `prop:thick-ssbnf-normal`,
`prop:linear-normal`, `prop:nonlinear-rs-example`,
`thm:main`, `thm:soundness`, `thm:complete`,
`thm:window-thick`, `thm:linear-poly`,
`lem:typed-thickness-bound`, `lem:window-typed-yield`,
and `lem:linear-short`. Several are notation-only. Others require semantic
comparison because the constructor was revised.

## New formal theorem supplied in this branch

`LeanCfgProject/TCS1/V128TypedLanguageEquality.lean` proves

`typedNonstartLanguage H ... A μ = untypedNonstartLanguage ... A ∩ {w | H.h w = μ}`

from the existing, non-axiomatic `untypedDerives_lift`,
`typedDerives_erase`, and `typedDerives_yield_type` proofs.

**Exact scope:** the untrimmed non-start SSBNF relation, with the same
terminal and binary rules and yield-typed grammar semantics. The manuscript
formula for *retained* symbols of a trimmed typed refinement still needs an
explicit bridge establishing removal of unproductive/inaccessible states does
not change the surviving symbol languages. The start-language equality likewise
needs its existing start-production semantics tied to this result.

## Further formalization added

`LeanCfgProject/TCS1/V128FiniteInformationClosure.lean` now contains a
product finite-monoid typing and candidate formal proofs of
`fixedHSubstitutable_inter_product` (Proposition 3.3(i)) and
`fixedHSubstitutable_regularFilter_product` (the distributional
substitutability part of Proposition 3.3(ii)).

These do **not** yet constitute full Proposition 3.3: the CFL closure
component and erasing inverse-homomorphism clause (iii) remain separate.
These branch additions were confirmed in CI #708 at the formal statement scope described above; this does not establish the full closure proposition or merger.

### Erasing inverse-image semantic kernel

`LeanCfgProject/TCS1/V128InverseImageKernel.lean` adds a candidate
formal proof that pulling back a substitutable language through an arbitrary
concatenation-preserving word map preserves distribution equality when
equal observed types include (a) equality of image h-types and
(b) agreement on whether images are empty. This treats the manuscript's
essential empty/nonempty split without assuming a nonerasing map.

**Remaining exact-statement gap:** Construct the two-element erasure monoid
`B_phi`, its homomorphism `e_phi`, and the finite product typing
`(h ∘ phi, e_phi)`, then derive these two hypotheses from equality
of the product observer. The context-free inverse-homomorphism closure
component is not internally formalized. The semantic kernel was built in CI #708. The concrete erasure observer is pending its own passing CI.

## v115/v116 semantic quotient and CFG presentation

Two new modules were added on this branch:

- `V128SubstringQuotient.lean`: candidate proof of language equality
  between the context-indexed v115 batch semantics and substring-indexed
  v116 batch semantics, *for all finite K*, including the empty-word case.
  The reverse simulation is strengthened to any observed occurrence.
- `V128SubstringCFGPresentation.lean`: candidate bidirectional semantic
  bridge between v116 inductive derivations and a conventional
  terminal/binary/unit grammar presentation on word-indexed states.

These are **not** a completed proof of the finite-state implementation size:
the displayed CFG has the infinite type `Word α` as carrier, although its
active productions are occurrence-guarded by finite K. A separate finite
observed-factor type/encoding and the O(n^4) size estimate remain open.

CI #708 confirmed the typed-language correction and the substring quotient and CFG presentation. The later finite-state grammar module built in CI #718. These checkpoints do not verify every claim of manuscript v128.

## Verified checkpoint and new pending work (2026-10-08)

Lean CI **#708** passed critical-path build, full `TCS1.All`, no-`sorry`,
and no project `axiom`. This certifies the then-present new modules:
typed non-start equality, finite-information intersection/filtering,
inverse-image semantic kernel, v115-v116 substring semantics and
binary-CFG presentation. It does **not** certify the entire v128 manuscript.

CI **#718** failed only on `V128ErasureFlagTyping.lean`, whose four
small multiplication goals and unit-value goal were amended in commit
`3ebba04c356422385e02f78600a00c8d40363d0b`.

CI #718 **successfully built** `V128FiniteSubstringGrammar.lean`:
the observed nonempty-factor Fintype, quadratic nonterminal count,
and its exact start-language equality with the previous batch semantics
(including epsilon). This does not certify a literal O(n^4) output encoding.

`V128ThicknessGapCore.lean` has now been added to encode precisely the
E_0 → a / E_(n+1) → E_n E_n | c derivation subfamily of
Proposition `prop:typed-thickness-gap`. Its candidate theorems show
one-letter ordinary yields, a c-free witness of length 2^n, and the
2^n lower bound on all c-free yields. A successful CI **after its import**
is still required. The full proposition additionally needs the source
family G_n, h_c-typed refinement, trimming, source-grammar size and
the typed-thickness definition.

For Proposition 3.3(iii), `V128ErasureFlagTyping.lean` now builds
the concrete two-element monoid and product observer as candidate code,
but must pass CI. The CFL-side closure statements are still open.

## Green CI checkpoint #726 and next gap-family bridge

CI run **#726 (37740560683)** at commit
`5d71f296f1b9ce62d0c315aedc3bde9ca5cb84e8` **passed**
the theorem-facing build, entire `LeanCfgProject.TCS1.All`, no-`sorry`
and project-`axiom` checks. The concrete two-element erasure flag
observer and `V128ThicknessGapCore` are hence machine-checked at their
formally stated scope. This does not imply full exact-v128 verification.

`V128ThicknessGapStartLanguage.lean` is a new, CI-*pending* extension
modeling U's four source productions, S₀ → U and D → c,
alongside the already-checked E-index derivations. It seeks to show
(i) L(G_n) = {a,c}^+, (ii) every no-c E_n yield is exponential and
there exists such a witness participating in a successful start tree,
(iii) one-letter E_i source yields, and (iv) linear production accounting.
A separate bridge to an explicitly constructed finite reduced SSBNF grammar
and trimmed h_c-typed refinement is still missing.

## Further typed-thickness integration — pending CI

`V128ThicknessGapStartLanguage.lean` models the explicit U productions
and proves at the derivation-semantics level that the start language is
`{a,c}⁺`, independently of n, and that the exponential E_n branch
occurs in a successful start derivation (U → E_n D).

`V128ThicknessGapTypedFiber.lean` defines a *fixed* two-element monoid
typing h_c (a ↦ 1, c ↦ 0), connects the h_c-unit fibre with absence of c,
and specializes the E_n exponential lower bound to that actual typing,
with a successful-tree witness. Both new modules are submitted for CI
and must not be represented as kernel-verified until a green run.

Still missing for the exact paper proposition: (i) a literal finite,
reduced SSBNF grammar carrying this indexed family, with full start,
production, productive and reachable semantics, (ii) the typed-refinement
trim-survival bridge, (iii) the exact formal typed-thickness definition
and source-size accounting. In particular do not infer
`τ_h^typ(G_n) ≥ 2^n` yet merely from the E-branch lemma.

## Retained typed non-start language equality — submitted for CI

`V128RetainedTypedLanguageEquality.lean` now contains a candidate
exact statement of v128 Proposition 5.2 for **every** retained
non-start symbol `(A, μ)` under the concrete productive/reachable trim:

`retainedTypedNonstartLanguage(A, μ) =
  untypedNonstartLanguage(A) ∩ {w | h(w) = μ}`.

It uses already verified `concreteTypedActive_trimClosure` to
restrict any full typed derivation rooted at an active state, while
`reducedTypedDerives_to_typedDerives` and
`typedDerives_yield_type` handle the reverse direction.
The **start-language** equality was previously verified in
`concreteTypedActive_language_eq_untyped`.
The new bridge itself must pass CI before it is called machine-verified.

CI #738 failed due to an unrecognized append nonemptiness helper in
`V128ThicknessGapStartLanguage.lean`, fixed in commit
`89a3c3f6f2068bb0c4d058d8a8f2c6b019516c2e`. The fix and
the retained-language theorem are subject to the next integrated CI.

## Successful typed branch trim-survival (pending CI)

The candidate module `V128TypedTrimSuccessfulBranch.lean`
reuses `ConcreteTypedActive` to prove a general start-branch bridge:
if a start child A has a binary rule A→BC and typed terminal
derivations for both children, then the two typed children are retained
by the productive/reachable trim and their **same derivations** survive
restriction. This is the precise structural principle needed to keep
(E_n)_1 alive along U→E_nD, once the full source grammar
G_n is encoded in the generic SSBNF formalization. It is not
the instance-specific exponential gap theorem yet. A green CI for the
new module is required before describing it as checked.

## Typed-thickness CI #764 green; ordinary source and reducedness under checking

**CI #764 (run 37753966708) passed** the TCS1 critical path, complete
`TCS1.All` build, no-`sorry`, and project-`axiom` checks. This
checks the *actual finite SSBNF family* (U,D,E_0,...,E_n) in
`V128ThicknessGapFiniteSSBNF.lean`, the E_n typed-unit witness
and its retention after trimming, plus
`V128ThicknessGapYieldBound.lean` which proves that **every**
uniform `YieldBound` for the trimmed typed non-start languages is
at least 2^n. Earlier #752 was the prior checkpoint, superseded by
this verified one.

`V128ThicknessGapOrdinary.lean` now contains candidate theorems:
every original source nonterminal has a one-letter yield, no
uniform original-language `YieldBound` can be zero, and the
ordinary-vs-typed thickness separation holds using the *same*
`YieldBound` interface.

`V128ThicknessGapReducedness.lean` now defines source nonterminal
graph reachability using the precise `GapBinaryRule` relation
and seeks to prove every U,D,E_i is reachable from the start child
U and productive, for all n including n=0.

**These last two modules are still CI-pending** (newest run #772).
The exact source production enumeration/encoded representation size
O(n), and unrelated remaining v128 statements, are not thereby
formally verified. The numerical `gapSourceRuleCount_linear`
arithmetic already in the library is not a counted-rule certificate.

## Gap production enumeration — source-rule correspondence (CI pending)

CI #774 failed only in `V128ThicknessGapReducedness.lean` at an
index coercion that needed an explicit `Fin.ext` natural-value goal.
The correction was committed as `ab0393a1`. CI #776 was superseded/
cancelled when further code was pushed; do not label it successful.

`V128ThicknessGapRuleEnumeration.lean` now defines a source-rule code
family (7 fixed and 2×n indexed), a decoder to **actual** terminal,
binary and start production datums, soundness of every decoded rule,
surjective coverage of each actual rule, and concrete enumerated-list
length `2*n+7` with an O(n) upper bound. Its intended scope is
the standard grammar-symbol counting convention where E_i counts as
an atomic nonterminal. The explicit `List.Nodup`/injectivity and
bit-level integer index encoding analyses are not yet formalized.
The code and the ordinary thickness/reducedness modules are now
awaiting the newest integrated CI #780.

## Gap proposition consolidation after green CI #786

The integrated **CI #786** (run `37786906358`, head
`35004c26d58ea5f2e50cbdeef28d6f5ba8fea88d`) passed all checks:
the theorem critical path, `TCS1.All` facade, no `sorry`, and
no project-level `axiom`.

Thus the concrete gap-example components now checked include:
- indexed finite SSBNF source grammar G_n and h_c typed-refinement;
- concrete productive/reachable trimming and retention of (E_n,1);
- all trimmed (E_n,1) derivations have yield length 2^n, hence
  every uniform typed `YieldBound` satisfies 2^n <= τ;
- source shortest yield `YieldBound` has minimum exactly 1;
- source reachable/productive symbols U,D,E_0,...,E_n;
- rule-code decoding sound/complete for all actual source productions,
  enumerated codes of length 2n+7, and
  `gapSourceGrammarSymbolBudget n <= 34*(n+1)`
  under atomic grammar-symbol counting.

Now **submitted but not yet CI-verified**:
- `V128ThicknessGapProposition.lean`: combines all five properties
  as `v128_exponential_typed_thickness_gap_package`;
- `V128ThicknessGapClassMembership.lean`: directly proves
  `{a,c}^+` is fixed-h substitutable and combines it with the
  source-grammar/language/size/thickness certificate in one theorem
  `v128_exponential_gap_manuscript_instance`.

The last two files are *pending a green run at their current commit*.
This is a proposition-level formalization only, **not** proof of all 30
v128 manuscript theorem environments. It does not cover alternative
symbol-index bit encodings and does not automatically certify a
complexity-theoretic algorithm-independent characteristic-data lower bound.

## Green CI #798: consolidated gap theorem; v116 cubic unary-rule bound in progress

**CI #798 (run 37790263534) succeeded:** integrated `TCS1.All`,
critical path, no `sorry`, no project-level `axiom`. The
single `v128_exponential_gap_manuscript_instance` theorem is verified:
the actual finite source gap grammar, start language `{a,c}⁺`,
fixed-h substitutability, source reducedness, ordinary thickness one,
the exponential trimmed-typed `YieldBound` lower bound, and an O(n)
atomic grammar-symbol budget. This verifies this *proposition-facing
package*, not the complete v128 manuscript.

For the **v116 O(n_K^4) explicit learner-output issue**, the v128
manuscript's argument is sharper than the legacy v88 quartic
pair-of-all-occurrence-slots count: it uses context/type buckets,
each having at most `|K|` entries, and total bucket membership
O(n_K²), giving **O(n_K³) unary U-rule candidates** and O(n_K⁴)
output size under literal O(n_K)-length per production.

`V128SubstringBucketCount.lean` has been added to:
- define actual observed-factor/context/type buckets;
- inject every factor in one fixed bucket into the sampled-word type,
  hence `|bucket| ≤ |K|`;
- formally prove the sum-of-squares cubic bound **conditional**
  on total bucket entries being at most the two-cut slot count.

**CI #802 pending** for the new file. The necessary unconditional
connection from the actual finitely enumerable bucket keys to a
two-cut occurrence-slot count and the final direct-production encoding
remains open. In particular the historical O(n_K⁵) direct bound
does not imply the revised v116 O(n_K⁴) claim.

## CI #818 green: exact v116 bucket-count delta and quartic candidate budget

**Lean CI #818 (run 37812248496), successful.** The full `TCS1.All`
facade, theorem critical path, no-`sorry` check and no project-level
`axiom` check passed on head `eec832f7a0dfefa3d0d422d1a8501c77d4dfa253`.

Thus the following NEW v116 delta theorems are now machine-checked:
- `SubstringContextBucket` has size at most `K.card`.
- All entries over arbitrary finite bucket keys inject into the
  previously checked `ReconstructionFactorSlot K`; total entries
  are at most the two-cut slot count (quadratic).
- `substringBucketKeys` is an explicitly finite image of the old
  factor-slot indexing space, and it covers **every** instance of
  `SubstringUnaryRelated H K x y`.
- `substringBucketKeys_unaryCandidateCount_le_cube` gives the
  unconditional `sum_B |B|² ≤ n_K³` for the enumerated bucket keys.

New code at the next head (NOT yet kernel verified):
`V128SubstringQuarticEnvelope.lean` reuses the old verified
`reconstructionSplitSlotCount_le_cube`,
`reconstructionFactorSlotCount_le_sq`,
`reconstructionSample_card_le_norm`, plus the new checked cubic
unary bound to form the precise **candidate-count budget**
`1+n_K+n_K²+2n_K³ ≤ 4(n_K+1)³`, and a bound
`4(n_K+1)⁴` after charging up to `n_K+1` symbols per
*enumerated candidate*. The candidate-count arithmetic has no
additional bucket-count hypothesis; the final literal written-rule
theorem still depends on a rule-count/encoding-length interface.

Do not confuse this envelope with a verified executable `B_h(K)`
emitter. Exact binding of the output writer to the revised v116 tables,
and its O(n_K⁴) *time* implementation (canonical factor IDs, fixed
h caching, key deduplication and rule checks), remains open.

## Green CI #836: literal v116 unary-production set, not yet effective end-to-end emitter

**2026-10-09 checkpoint.** `V128SubstringUnaryRuleTable.lean` was added on the Draft PR #8 branch, imported into `TCS1.All`, and verified by [CI #836](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37818506991) (run `37818506991`, checked commit `d98cf514709bcefbdb6f65ead19498e71311e315`). This CI passed: targeted v128 unary module, legacy theorem critical path, integrated `TCS1.All`, no-`sorry`, and no project `axiom`.

The NEW machine-checked declarations are:

- `v116UnaryRuleTable_sound`: every (x,y) in the finite emitted (U) table satisfies the actual `SubstringUnaryRelated` predicate.
- `v116UnaryRuleTable_complete`: every v116 semantic unary rule (x,y) is present in the table.
- `v116UnaryRuleTable_iff`: literal table membership is equivalent to `finiteSubstringGrammar.unitRule` for observed-factor states.
- `v116UnaryCandidate_card_eq` and `v116UnaryRuleTable_card_le_cube`: a concrete `Finset` of (U) productions has cardinality at most `(reconstructionSampleNorm K)^3`. Unlike the previous candidate envelope, this bound applies to the *actual finite unary table*.

These theorems use the existing finite bucket enumeration and its verified cubic bound, not a reimplementation of the v88 learning/complexity proof. The `Finset` is **noncomputable** because its finite indexed state/bucket presentation uses classical choice. Therefore this is a literal finite mathematical production set with proven soundness, completeness and size, **not** a verified executable enumerator / deduplicator / serializer and **not** the claimed `O(n_K^4)` time theorem.

Remaining output bridge: B/L/S/epsilon literal tables, start-rule/epsilon integration, canonical finite factor identifiers and context IDs, effective type-cache and stable deduplication, per-rule encoding size bound, and machine-step work proof. Other outstanding v128 exact-version claims (`prop:li-window`, `cor:li-thickness`, full finite-information closure and all 30 environments) remain as documented below.

Historical CI #828 was an infrastructure-only DNS failure during elan setup; CI #831 exposed two new Lean type errors subsequently repaired. #836 supersedes both as the last fully green **code** checkpoint. A documentation-only commit after #836 does not extend its proof coverage.

## CI #858 GREEN: exact finite B/U/L/S/epsilon tables and batch-language semantics

**2026-10-09:** [CI #858](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37822000555) SUCCESS, run `37822000555`, code SHA `06fe94b6307adee3b62222c0f9a0f35664e85f20`. New targeted table/grammar modules, historical theorem-facing critical path, complete `TCS1.All`, no-`sorry` and no-project-`axiom` gates ALL passed.

New verified modules:
- `V128SubstringRemainingRuleTables.lean` supplies actual finite sets for (B) binary, (L) lexical, (S) start and epsilon-start, plus precise iff lemmas against `finiteSubstringGrammar`; non-start epsilon rules are absent. The v116 (U) table and cubic actual U-table cardinal bound were already checked at CI #836.
- `V128SubstringTabulatedGrammar.lean` forms `v116TabulatedNonstartGrammar` by using membership in those materialized finite B/U/L sets as production predicates, proves both `v116TabulatedDerives_to_finiteCFG` and `finiteCFG_to_v116TabulatedDerives`, and combines start/epsilon table correspondence with the earlier certified quotient to give `v116TabulatedBatchLanguage_eq_batchLanguage`. This equality is quantified over **every** finite K (including K empty and epsilon in K).

Precise limitation:
- These are noncomputable mathematical `Finset` materializations and verified semantic extensional equality, **not** a verified effective construction with quartic machine-step complexity. In particular B currently filters the full observed-state **triple** universe. That is not the manuscript's three-cut O(n_K^3) candidate enumerator, even though both denote exactly the same binary-rule set.
- Next formal delta must enumerate B from the existing `ReconstructionSplitSlot K` rather than the broad triple universe and prove sound/complete correspondence. Reuse its already verified `reconstructionSplitSlot_card_le_cube`, then attach L/S/epsilon/U actual effective candidate traversal, canonical factor/context IDs, caching, deduplication, encoding length and runtime. Do not silently discharge `thm:poly-build` or the conditional `substringV116WrittenRules_le_quartic` with cardinality alone.
- Exact-v128 theorem-environment audit, locally trivial finite-window criterion and characteristic-data corollary remain pending.
- CI #849 initially failed one epsilon-table membership simp goal; explicit membership case split fixed it before #858.

Documentation commits after the certified code SHA are not an independent verification of a changed Lean proof. PR #8 remains Draft; v88 official release and TCS submitted manuscript are untouched.

## CI #877 GREEN: cubic cardinality of the *actual* finite v116 binary production set

**2026-10-09 code checkpoint:** [CI #877](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37826408393), run `37826408393`, verified Lean SHA `d4d61165f950713af141ebec291b5a6ef344f037`. All checks passed: focused new-delta build, theorem-facing critical path, integrated `TCS1.All`, absence of `sorry` and absence of project-level `axiom`.

Added `V128SubstringBinarySplitSlots.lean`:
- `v116BinarySplitCode` decodes each old `ReconstructionSplitSlot K` as a potential `(parent,left,right)` word triple; `v116BinarySplitCodes` takes its finite image.
- `v116BinarySplitCodes_cover` proves every **actual** B production from `v116BinaryRuleTable K` has a witness in that finite three-cut candidate image. The raw candidate set deliberately includes some invalid/reversed/empty splits, which must **not** be emitted as real rules without a validity check.
- `v116BinarySplitCodes_card_le_cube` uses the old proved `reconstructionSplitSlot_card_le_cube`.
- `v116BinaryProductionWordCode_injective` proves unique factor-word identifiers preserve entire binary rows. `v116ActualBinaryRule_has_split_slot` plus `v116ActualBinaryRuleToSplitSlot_injective` choose a witness three-cut slot per actual rule and prove an injection into the old candidate space. Thus **`v116BinaryRuleTable_card_le_cube` unconditionally proves that the actual B production count is at most `(reconstructionSampleNorm K)^3`**. This is a stronger actual-table result than the previous standalone *candidate* envelope.

This reuses the v88 split-slot cardinality bound and the CI #858 verified literal rule tables and semantic language equivalence, with no changes to historical proof modules. The same cubic actual U-rule bound was certified at CI #836.

**Still missing for the exact polynomial-reconstruction theorem:** A genuinely effective scan/filter/deduplication/serialization algorithm, rather than a noncomputable image and `Classical.choose` representative; canonical state/context identifiers and cached `h` evaluation; quantified work/encoding per emitted rule; a complete end-to-end `O(n_K^4)` machine-step certificate. Cardinality ≤ cubic by itself is *not* a runtime proof. The locally trivial image theorem, characteristic-data corollary and exact-v128 thirty-theorem audit remain open independently.

CI fixes on the route to green: #869 length normalization, #873 filter membership and List-take normalization, #875 explicit standard `List.take_append_length` lemma. #877 passed.

Documentation commits after the verified code SHA may have their own pending CI; do not silently extend proof coverage from them.

## CI #890 GREEN: computable (B) enumeration is extensionally exact

**2026-10-09 checkpoint.** [CI #890](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37830187537) is fully SUCCESS at Lean code SHA `e7858324859765065598255ac36cb747aff599e8` (focused module build, unchanged theorem-facing critical path, integrated `TCS1.All`, no-`sorry` and no-project-`axiom` gates).

New `V128SubstringEffectiveBinaryTable.lean` closes the **computability and correctness** gap for the binary **word-code** rule set:
- `v116EffectiveObservedFactorWords` is a computable two-cut `Finset` scan, with `v116EffectiveObservedFactorWords_iff` proving exact agreement with nonempty observed factors, rejecting invalid occurrences.
- `v116EffectiveRawBinaryCodes` is a computable three-cut candidate image; `v116EffectiveRawBinaryCodes_eq` equates it to the previous CI #877 raw candidate set.
- `v116EffectiveBinaryWordTable` is an ordinary computable `Finset.filter` of those candidate triples, checking parent = left ++ right, both children nonempty and parent present among the observed factor words.
- `v116EffectiveBinaryWordTable_iff` characterizes the output by exactly the semantic v116 (B) rule predicate. Crucially, **`v116EffectiveBinaryWordTable_eq_actual`** proves equality with the image of the older finite materialized `v116BinaryRuleTable K` under `v116BinaryProductionWordCode`. No arbitrary invalid split is emitted. This is a verified bridge from **effective finite enumeration** to **semantic CFG rules**.
- `v116EffectiveBinaryWordTable_card_le_cube` proves this effective table contains at most `(reconstructionSampleNorm K)^3` different word-coded productions, reusing verified cubic three-cut enumeration.
- The noncomputable older table and earlier semantics/derivations were **not modified or re-proved**. Both current effective B and older noncomputable B denote exactly the same rules.

**Important strict scope:** Compiling these Lean `def`s without `noncomputable` plus proving their output correct is NOT a certified worst-case machine-step bound. The `Finset` construction may redo factor scans and its `image`/comparison/dedup/serialization cost has not been bounded. A literal output representation with stable canonical state IDs (or a justified duplicate-tolerant rule-list semantics), a cached finite-monoid `h` table, and effective U/L/S/epsilon production emitters with explicit per-stage step costs remain necessary. In the manuscript `thm:poly-build`, cardinality of B and U candidates is cubic, fixed-monoid values are cached via O(n²) extensions, and emitted rules may cost O(n) in literal encoding. None of the corresponding time-accounting assumptions should be silently replaced by Finset-cardinality alone. This also does not close `prop:li-window` or the characteristic-data result, and v128's 30-statement exact audit remains incomplete.

Initial CI #887 failed three `Observed` / list-associativity proof simplifications, #888 narrowed this to two list-parenthesization obligations, and CI #890 passed after the corrections. Subsequent documentation-only commits must not be counted as a new Lean proof checkpoint until their own CI is checked.

## CI #901 GREEN: source-exact 30-row first-pass crosswalk; two genuine open Lean claims

New [`V128_NUMBERED_CLAIMS_ONE_TO_ONE_AUDIT_2026-10-09.md`](./V128_NUMBERED_CLAIMS_ONE_TO_ONE_AUDIT_2026-10-09.md) extracts all **30 numbered mathematical statement environments** in the **current v128** `Papers/01_fixed-h-cfg/main.tex`, including the one unlabeled corollary. It maps every item to **explicit existing Lean mathematical theorem names**, records the specific v128 delta and separates external standard facts.

New `LeanCfgProject/TCS1/V128ThirtyClaimCrosswalk.lean` has 30 ordered entries and **65 `#check` occurrences**. [CI #901](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37846653643) SUCCESS at code SHA `9605407fefad5bf94b34cd83aa4fd504966e03ac`, including focused crosswalk build, old theorem-facing critical path, integrated `TCS1.All`, no-`sorry`, no-project-`axiom` gates.

Classification: **24 reusable theorem sources (R)**; **3 v128 bridges (B)**: main theorem packaging, Gold corollary packaging, reconstruction polynomial/quartic algorithmic comparison; **1 partially formalized proposition (P)**: finite-information closure (RS component all clauses complete but the ordinary CFL closure ingredients not made into internal Lean types); **2 open (O)**: `prop:li-window` (locally trivial positive image iff some fixed-window positive-word kernel refinement, explicit `(n,n)`, local triviality of window image, union characterization), `cor:li-thickness` (locally trivial typed-thickness/characteristic-data transfer). `thm:main` item (iv) depends on the two open cases.

**No old Lean proofs were replaced or invalidated.** The v79/v88 executable learner, materialized production table, CYK membership, Gold stabilization, combinatorial scan/candidate envelopes, typed-thickness/witness and linear/fixed-window results survive and are reused. Low-level CPU/Lean evaluator small-step cost semantics was **explicitly outside** the older project's stated boundary. The v128 direct B/U cubic candidates and quartic literal-output budget still need a concrete O(n_K^4) v116 algorithmic **operation-accounting bridge**; this is distinct from implementing a machine-code operational semantics.

A `#check` only typechecks an existing proof declaration; it does not automatically establish textual equivalence with the v128 quantifiers and exact hypotheses. Accordingly this is a **first-pass complete mapping of all 30 environments**, **not** a declaration that the entire exact v128 has been internally verified. Full theorem-type equivalence, assumptions/axiom dependency and unnumbered mathematical exposition remain to be checked.

## Blocking obligations for a genuine v128 checkpoint

1. **Constructor correspondence and effective runtime.** The v115-v116 derivation quotient and finite observed-factor CFG were checked earlier; the literal finite B/U/L/S/epsilon tables and exact start-language equality were checked at CI #858. The remaining obligation is **computable** split-slot-indexed production enumeration (rather than the present broad triple-state filter), O(n^4) encoded-size and step-count certificates, and an exact comparison with every condition of the v128 algorithm.
2. **Typed-refinement retained-symbol bridge.** Connect the new language
   equality to the trimmed, reachable non-start symbols of Proposition 5.2 and
   to full `L(\widetilde G)=L(G)`.
3. **Finite-information closure.** Confirm the new product/intersection and filter Lean code builds, then formalize the remaining CFL-closure bridge and erasing inverse image with the empty-image flag in Proposition 3.3(iii).
4. **Locally trivial criterion.** Formalize Proposition 3.5, including
   `n = |h(Σ+)| + 1`, `(n,n)` window selection, and both kernel directions.
   The classical semigroup criterion should remain attributed to Pin.
5. **Exponential typed-thickness gap.** Construct exact indexed families,
   show reduced SSBNF, source size O(n), ordinary thickness 1,
   and typed thickness >= 2^n.
6. **Locally trivial characteristic data.** Prove Corollary 7.4 via
   fixed-window bounds, normalization, type-preserving transfer, and its
   nonempty-target scope.
7. **Remaining theorem statements.** Check all 30 present labeled theorem
   environments, plus mathematically substantive unnumbered claims, with
   exact formal statement correspondences rather than only `#check` and a
   `True` marker. Verify the main theorem's nonempty language scope,
   conservative learner, characteristicity, and polynomial claims.
8. **CI gate.** Build the new module and full `LeanCfgProject.TCS1.All`,
   prohibit `sorry` and project axioms, attach CI job/run evidence. CI for
   this branch must be inspected before any verified claim.

## Publication hygiene

This work is an internal mathematical audit. Do not silently add Lean or
Zenodo references to the TCS revised manuscript or response, which
deliberately omit them. Keep the verified v88 release immutable.
