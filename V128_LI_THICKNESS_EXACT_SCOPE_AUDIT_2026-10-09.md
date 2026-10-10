# TCS #1 v128: manuscript-exact review of local-triviality thickness and main theorem (iv)

Date: 2026-10-09. **Audit, not a claim of complete formalization.** Source manuscript: `growupkuriyama-hub/Papers/01_fixed-h-cfg/main.tex` (retrieved 2026-10-09). CI verified core: [#954 success](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/37915613488), code SHA `0839dca9b0f3279ab7954bee90f0bdd8b663c859`.

## Exact manuscript claims

- **`prop:li-window`** (around source line 583): **nonempty alphabet**; finite-monoid morphism `h`; `n := |h(Σ⁺)|+1`; local triviality of positive image iff some positive-word `ker(h_{k,l}) ⊆ ker(h)`; explicit `(n,n)`; every concrete window typing has locally trivial positive image; `KL(Σ) = ⋃_{positive-image locally trivial h} RS_h(Σ)`; same after intersecting CFL.
- **`cor:li-thickness`** (around source line 1253): for **every nonempty** `L ∈ C_h` represented by an **arbitrary reduced CFG** `G_*`, characteristic data for `B_h` have **encoded size polynomial in both `|G_*|` and ordinary `τ_{G_*}`**. Excludes the empty target from the quantifier (handled separately). Constants may depend on fixed `h, Σ`; no uniform bound for variable window parameters, no converse, no incremental polynomial-data guarantee.
- **`thm:main` (iv)** (around source line 573): the same bound quantified over any reduced CFG presenting each nonempty target under locally trivial positive image, as part of the unified learner theorem.

## Precisely what CI #954 verifies

1. `V128PositiveWindowKernelForward.lean` and `V128PositiveWindowKernelConverse.lean` provide the positive-word kernel iff, explicit window, positive image idempotent argument, fixed-window concrete typing, and pointwise fixed-window substitutability transfers. These are real Lean theorems (no `sorry` / project axioms) and pass the full facade build.
2. `V128LocallyTrivialThickness.lean` proves an **SSBNF-presentation conditional**: given the original typed reconstruction hypotheses, a uniform ordinary short-derivation bound `∀ A : N, ∃ z, UntypedDerives A z ∧ |z|≤τ`, finite index types, `hsub`, and the *already supplied* quantitative comparison `τ ≤ ssbnfThicknessEnvelope cV c₁ sourceSize τR`, the characteristic sample built over **original H** reconstructs the untyped target exactly and has an encoded-norm envelope `fixedWindowGrammarSizeEnvelope |M| (2n) gBound (ssbnfThicknessEnvelope ...)`.
3. `FixedWindowCharacteristicDataFacade.lean` supplies the pre-existing fixed-window sample estimate and reconstruction package. The fresh theorem reuses this package instead of reproducing old proof.
4. CI #954 passed critical path, `TCS1.All`, no-sorry and no-project-axiom gates.

## Outstanding *logical* bridge; do not hide in a theorem name

To prove the **paper's exact corollary**, an additional theorem/package must start from an arbitrary reduced CFG `G_*` producing nonempty `L`, and construct or exhibit an equivalent **reduced SSBNF `G`** with:
- `L(G)=L(G_*)` and the original `h`-substitutability condition transported to `G`;
- the normalization bounds `|G| ≤ q_size(|G_*|)` and `τ_G ≤ q_thick(|G_*|, τ_{G_*}+1)`;
- corresponding `hshort` for all relevant untyped nonterminals after normalization, plus finite typed indices;
- the grammar size / rule-count `gBound` controlled by `|G_*|`;
- `fixedWindowMinimalCanonicalSample` for this `G` interpreted as characteristic data **for the same target** and the stated encoded size (not merely a symbolic bound depending on unconstrained `gBound, cV, c₁`).

The audited Lean theorem has **`hτ`, `hg`, `hN`, `ht`, `hb`, and `hshort` as hypotheses**. It proves their consequence; it **does not establish those hypotheses from an arbitrary reduced CFG**. In particular an envelope expression alone is not a polynomial-time algorithm or even a polynomial upper bound until the parameters are bounded by the source grammar.

For `thm:main`(iv), additionally transport the characteristic-data package into the chosen `B_h` of the main learner theorem and prove its theorem-level quantified formulation. This is distinct from showing a single finite batch equality.

## Next proof units in dependency order

1. Audit any existing `prop:thick-ssbnf-normal` Lean formalization for source CFG → reduced SSBNF, nonempty-target, ordinary-thickness, and explicit bound witnesses. If absent, add a separate **constructive normalized-grammar** interface and prove its clauses, not an axiom or unproved typeclass witness.
2. Derive source-size/rule-count bounds and the `hshort` target from that normalization interface.
3. Specialize `locallyTrivialCharacteristicData_ssbnf_package`, discharge **all** quantitative hypotheses, and prove paper-facing corollary with the actual size polynomial.
4. Connect the resulting characteristic sample to `thm:main`(iv) and to the 30-item exact-version crosswalk, noting nonempty alphabet and nonempty target explicitly.
5. Keep `O(n_K^4)` executable construction accounting separate from the characteristic-sample size theorem; CI #954 does not close it.

This audit supersedes the older status message saying only `cor:li-thickness` remains, and does **not** alter the paper, main branch, or v88 release.
