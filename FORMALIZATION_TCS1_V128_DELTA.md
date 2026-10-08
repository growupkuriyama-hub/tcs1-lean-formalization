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
