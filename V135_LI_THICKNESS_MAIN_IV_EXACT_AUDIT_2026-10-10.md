# TCS #1 v135 — `cor:li-thickness` / `thm:main`(iv): manuscript-exact Lean audit (2026-10-10)

> **Status: the statements below are Lean theorems that passed CI.** Latest GREEN containing them: `d130c3d` (CI #1008). First verified at code SHA
> `51e895d` — [CI #1000](https://github.com/growupkuriyama-hub/tcs1-lean-formalization/actions/runs/38013389121) **SUCCESS**
> (v128 delta build, theorem-facing critical path, `LeanCfgProject.TCS1.All`, no-`sorry`, no-project-`axiom`).
> Manuscript: `growupkuriyama-hub/Papers/01_fixed-h-cfg/main.tex`, internal **v135**, sha256 `e8590799dbb889f6a375f61c6b9f8c00f3c23d6691d73561808d0989e450ecad`
> (Papers commit `2e67f3a`). Supersedes the "outstanding bridge" section of `V128_LI_THICKNESS_EXACT_SCOPE_AUDIT_2026-10-09.md`.

## 1. Manuscript statements (verbatim scope)

- **`cor:li-thickness`**: fix `h : Σ* → M`, `h(Σ⁺)` locally trivial. Every nonempty `L ∈ C_h` represented by a reduced CFG `G_*` has characteristic data for `B_h` of encoded size polynomial in `|G_*|` and `τ_{G_*}`.
- **`thm:main`(iv)**: if `h(Σ⁺)` is locally trivial, then for every nonempty target the sample in (ii) can be chosen polynomial in `|G_*|` and `τ_{G_*}` for any reduced CFG `G_*` representing that target; in particular for every `h_{k,ℓ}`. Polynomials may depend on fixed `h, Σ`, not on `G_*`.
- Conventions (§2): characteristic sample `C ⊆ L` with `C ⊆ K ⊆ L ⇒ L(B(K)) = L` for every finite `K`; `‖K‖ = Σ_{w∈K}(|w|+1)`; `τ_G = max_A min{|w| : A ⇒* w}`; `|G|` a reasonable encoding polynomially equivalent to the usual symbol count.

**v128 → v135 drift check:** all 32 numbered environments (30 claims + 2 definitions) and all 30 proof bodies are textually identical (whitespace-normalised) between v128 blob `07c53aa9…` and v135. v129–v135 changed introduction/prior-art prose, the new example `L={a,aa}` (v134), relocation of Yoshinaka's `L₀`, one wording change ("needed" → "used in the present completeness proof"), and bibliography only.

## 2. Lean theorems (all in `LeanCfgProject/TCS1/`)

| Lean declaration | File | Content |
|---|---|---|
| `cor_liThickness_exact` | `V135LiThicknessExactCorollary.lean` | `∃ c d, c = corLiThicknessConst H ∧ d = 12 ∧ ∀ {N P} [Fintype N] [Fintype P] [DecidableEq N] (G : IndexedMixedCFG N α P) (S), IndexedMixedReduced G S → FixedHSubstitutable H L → L.Nonempty ∧ ∃ K, IsSetDrivenCharacteristicSample (BatchLanguage H) L K ∧ ‖K‖ ≤ c·(G.symbolCount + G.ordinaryThickness + 1)^d`, where `L = MixedNonterminalLanguage G.toMixedRules S` |
| `cor_liThickness_bound` | same | per-grammar form with the constants already fixed |
| `corLiThicknessConst H` | same | `liEnvelopeConst |M| (2n) · (|Σ|+2)^12`, `n = |h(Σ⁺)|+1` — depends only on `H` and `Σ` |
| `thm_main_item_iv` | `V135MainTheoremItemIV.lean` | the above **plus** Gold identification by the verified materialized conservative learner on every positive presentation (reused `indexedFixedH_learning_materialized_core`), for the same `B_h` |
| `thm_main_item_iv_fixedWindow` | same | item (iv) for every concrete `h_{k,ℓ}` (via verified `fixedWindow_positiveImageTrivial`) |
| `V135AxiomAudit.lean` | — | `#guard_msgs` + `#print axioms`: the four theorems above depend exactly on `[propext, Classical.choice, Quot.sound]`; any `sorryAx` or project axiom would fail the build |
| helper results | `V135LiThicknessExactCorollary.lean` | `leastClosedLanguage_eq_mixedNonterminalLanguage`; `IndexedMixedCFG.ordinaryThickness` with `ordinaryThickness_thicknessAtMost` (attained) and `ordinaryThickness_le_of_thicknessAtMost` (least); `IndexedMixedCFG.symbolCount` and `normalizationScale_le_symbolCount`; `liThicknessEnvelope_le_poly`; `isSetDrivenCharacteristicSample_of_batch_eq` |

Fixed in the same session (CI-verified at #1000):
`MixedDerivationLeastClosedBridge.lean` (mutual recursion failed termination inference; now proved via `MixedDerives.rec`/`MixedSymbolsDerive.rec`, statements unchanged) and confirmation that `7ff0602`'s `GeneralCFGDerivationBridge.lean` termination fix compiles.

## 3. The ten audit questions

1. **Reducedness ⇒ productivity.** `IndexedMixedReduced G S` is literally "every nonterminal reachable from `S` (dependency graph) and productive (has a successful parse tree)". Productivity is used directly (`hred.2`).
2. **Nonempty start language without extra hypothesis.** Derived: `hred.2 S`. The theorem even *concludes* `L.Nonempty`.
3. **`{ε}` target.** Covered: `indexedLocallyTrivialCharacteristicData_nonempty_package` branches on whether `L` has a nonempty word; the `{[]}` sample is used otherwise (`singletonEpsilon_characteristic`); the `+1` in the envelope covers its norm. No separate hypothesis.
4. **Normalized grammar = source language.** Internal to the verified pipeline (`IndexedNormalizationLanguage`, `indexedFixedHCanonicalSample_characteristic`). The final conclusion is stated about the *source* language `L`, so no unverified equivalence can leak into the statement.
5. **Transfer of `H`-substitutability.** The only substitutability hypothesis is on the source language `L`; the normalized grammar generates the same `L` (item 4).
6. **Reconstruction typing is the original `H`.** The conclusion is `IsSetDrivenCharacteristicSample (BatchLanguage H) …`. The window typing `h_{n,n}` enters only the *size bound* (through `positiveWindowBound H` in the constant).
7. **Polynomial bound.** Proved: `‖K‖ ≤ c·(|G_*| + τ_{G_*} + 1)^12` with `c = corLiThicknessConst H`. `c` and the degree are chosen before the grammar is quantified, so they cannot depend on `G_*`.
8. **Hidden assumptions.** Hypotheses are exactly: `PositiveImageSandwichTrivial H` (local triviality of `h(Σ⁺)`: `e·s·e = e` for idempotent `e`, any `s ∈ h(Σ⁺)`), reducedness, `H`-substitutability. Finiteness of `N, P, Σ, M` is part of "finite CFG / finite monoid". `#guard_msgs` checks the kernel axiom set.
9. **Quantifier "any reduced CFG `G_*`".** Lean quantifies over **all** finite indexed CFGs (`IndexedMixedCFG N α P`: arbitrary finite production index, arbitrary RHS lengths including ε- and unit rules) over arbitrary universes, with any start symbol. A paper CFG `(V,Σ,P,S)` is the instance `N := V`, `P := P`. `|G_*|` is the usual symbol count `Σ_p (1+|rhs p|)` (the paper fixes it only up to polynomial equivalence; this is a convention, not a theorem). `τ_{G_*}` is the exact max–min (`ordinaryThickness`), not an upper-bound parameter.
10. **Characteristic data definition.** `IsSetDrivenCharacteristicSample B L C := ↑C ⊆ L ∧ ∀ K, C ⊆ K → ↑K ⊆ L → B K = L` is the §2 definition verbatim, with `B K` the language of `B_h(K)`. Obtained from exact reconstruction via verified soundness (`batchLanguage_sound`) and monotonicity (`batchLanguage_exact_of_characteristic_subset`).

## 4. What is *not* claimed

- **Polynomial time of normalization** (`prop:thick-ssbnf-normal`'s "in polynomial time"): not part of item (iv) / the corollary; the Lean normalization is a verified construction with verified size/thickness bounds, not a time-bounded algorithm.
- The degree 12 is an artefact of the verified envelopes, not an optimized exponent.
- `thm:main` items (i)–(iii), (v) remain as in the existing `MainTheorem*Package` modules; this audit adds (iv) only.
- The manuscript's `B_h` is the v116 tabulated substring grammar; its language equals `BatchLanguage H K` for every `K` (`v116TabulatedBatchLanguage_eq_batchLanguage`, CI #858). The transfer theorem `cor_liThickness_bound_v116` (`V135ItemIVv116Operator.lean`) passed CI #1004 and again #1008.
