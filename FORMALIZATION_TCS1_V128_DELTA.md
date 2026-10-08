# TCS #1 v128 — exact-version Lean delta audit (IN PROGRESS)

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

## Blocking obligations for a genuine v128 checkpoint

1. **Constructor correspondence.** The v115-v116 derivation quotient and start-language equivalence for all finite K were checked in CI #708; the finite observed-factor CFG and start-language equivalence built in CI #718. The remaining obligation is literal finite production enumeration and O(n^4) encoded-size analysis, plus a final exact comparison with every condition of the v128 algorithm.
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
