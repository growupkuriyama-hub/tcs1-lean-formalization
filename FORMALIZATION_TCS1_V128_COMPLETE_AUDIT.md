# TCS #1 v128 complete Lean re-verification ledger

Status: **COMPLETE — v128 exact-source CI and the full TCS1 facade CI are green.**

## Frozen manuscript source

English source of truth:

- paper repository: `growupkuriyama-hub/Papers`
- source file: `01_fixed-h-cfg/main.tex`
- last commit changing the frozen English source:
  `3ad4aacda70de6208bf9f82de19518048f39dd51`
- source blob SHA:
  `e503bfc7b86c963d7ff3b52c3158b06ea9c10c6f`
- source SHA-256:
  `cb18358871d34f6120fed03bc9da7bfed5f1f3095487cca03b07d40ae4d90128`
- baseline metadata commit after final EN/JP synchronization:
  `283cc2cf18b6a0c52e48607247e18b280eb31f7c`
- internal paper version: **v128**
- theorem/proposition/lemma/corollary environments: **30**

The v128 source differs from the previously audited line only by reviewer-facing
precision edits.  The mathematically relevant additions are audited explicitly:

1. the locally-trivial characteristic-data statement is scoped to nonempty
   targets, while the empty target is handled by the empty sample;
2. the comparison with Yoshinaka's unary rules spells out the tagged
   fixed-window long-word cutoff
   `max{1,k+l}` for distinct factors;
3. attribution and terminology sentences were sharpened without adding a new
   theorem.

## Lean source

- repository: `growupkuriyama-hub/tcs1-lean-formalization`
- branch: `tcs1-v128-complete-reverification`
- inherited full mathematical audit: `V126ExactSourceAudit.lean`
- v128 precision audit: `V128SourcePrecisionAudit.lean`
- aggregate exact-source gate: `V128ExactSourceAudit.lean`

The v126 theorem modules remain the proof-bearing implementation for unchanged
mathematics.  v128 adds only source-facing precision theorems instead of
duplicating already checked proofs.

## v128-specific obligations

| Claim | Lean evidence | Status |
|---|---|---|
| cutoff is exactly `max 1 (k+l)` | `v128_fixedWindowThreshold_exact` | Internal |
| for distinct factors, equal `h_{k,l}` type iff both are long and share the required prefix/suffix | `v128_fixedWindow_type_eq_iff_long_of_ne` | Internal |
| empty sample reconstructs the empty target exactly | `v128_batchLanguage_empty_sample` | Internal |
| empty target therefore has exact characteristic sample `C=empty` | `v128_empty_target_handled_by_empty_sample` | Internal |
| all 30 numbered theorem environments and post-v88 unnumbered claims | inherited `V126ExactSourceAudit` plus the two v128 modules above | Internal/Bridged except explicit literature boundaries below |

## Explicit literature/background boundaries

These are intentionally **not** represented by project axioms.

- Standard CFL closure under regular intersection and inverse homomorphism.
- Gold's classical superfinite-family obstruction.
- Yoshinaka's previously published fixed-window counterexample `L0`.
- Pin's finite-semigroup factorization `S^n = S E(S) S`; every
  paper-specific step after that input is Lean-checked in
  `V126PinFactorizationBridge`.
- Classical deterministic-context-free classifications used as adjectives for
  the uncapped counter, one-bracket Dyck language, and the Delta-star example.
  The paper-specific deterministic scanner and exact Delta-star semantics are
  Lean-checked; no Mathlib DPDA object is claimed.
- The classical characterization of linear languages by one-turn pushdown
  automata, used only as background attribution.

## Completion gate

The phrase **“v128 manuscript Lean re-verification complete”** is permitted
only when all of the following hold:

1. `V128ExactSourceAudit.lean` builds on the frozen source-matching branch;
2. `LeanCfgProject.TCS1.All` builds on the same branch head;
3. the repository-wide no-`sorry` / no project-level `axiom` checks pass;
4. the paper source SHA-256 still equals the frozen value above;
5. no new source commit has changed `main.tex` since the frozen commit.

A green CI alone is not a completeness argument; the source freeze and the
claim ledger are part of the gate.


## Completed verification run

The proof-bearing branch passed both release gates before this ledger-only
status update:

- `TCS1 v128 exact-source verification`: success
- `TCS1 Lean CI`: success
- theorem-facing critical path: success
- `LeanCfgProject.TCS1.All`: success
- repository TCS1 `sorry` scan: success
- project-level `axiom` scan: success

This final ledger update changes no Lean declaration.  The same gates are
triggered again on the ledger-final branch head so that the archived final HEAD
itself is green.
