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
These branch additions have not been independently confirmed by a successful
GitHub Actions run, so their status is **Lean code submitted for checking**,
not machine-checked or merged.

## Blocking obligations for a genuine v128 checkpoint

1. **Constructor correspondence.** Prove the v116 substring-indexed quotient
   constructor `B_h(K)` language-equivalent to the v88 context-indexed
   reconstruction, for every finite sample including the empty sample. A prose
   equivalence memo is not an exact Lean theorem.
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
