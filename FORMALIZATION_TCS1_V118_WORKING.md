# TCS #1 v118 — Lean source-delta audit (NOT a proof certificate)

Date: 2026-10-07. Draft / unmerged working branch.
Authoritative manuscript: `growupkuriyama-hub/Papers/01_fixed-h-cfg/main.tex`.
`PAPER.yaml` records **internal version v118** and English source
SHA-256 `54e40e28e8387d04d42339aed5a4ef6240729da4ea698ab4ee77e5f794ec0183`
(Japanese source SHA-256
`66a8de4857ef70c95877c561eae6804d54461d0cc32cf3ee69a862079d2693ee`).
Latest English source-changing commit observed:
`d785445f8c4207bad1b53c0b852c23161a1fad2f`.
Previous v117 manuscript source-changing commit:
`33220b2ed701490acf5d43799788cff5cff4abd7`.

This is a TCS **major-revision working version**, NOT evidence that
the updated submission has been sent to the journal.
The v117 source audit is separately preserved in
`FORMALIZATION_TCS1_V117_WORKING.md`.

## Source crosswalk

The 31 English theorem/proposition/lemma/corollary environments retain
the v117 theorem-label surface; the Japanese manuscript also has
31 such environments. The v116 **substring-indexed** B/U/L/S
reconstruction rules and its batch semantics are unchanged.
`v116_batchLanguage_eq_v115` is the previously machine-checked
quotient bridge; do not infer from it that all v118 source claims
have been verified.

Source changes that must be considered, even when an environment label
and statement remain the same:

1. Proposition `prop:li-window`: the forward implication uses a **new
   direct proof** for locally trivial positive semigroups. With
   `S=h(Σ+)` and `n=|S|`, products of `n` elements contain an
   idempotent factor; local triviality gives `e z f = e f` for
   idempotents `e,f` and `z∈S¹`, and then `h(prq)=h(pq)`
   when `|p|=|q|=n`. The former specific Pin locators were
   removed. Check the finite factorization lemma, treatment of empty
   middle words, and the exact induced kernel refinement.
2. The Section 8 nonregular linear witness is now additionally
   obtained as a **regular filter**
   `L_{±,e}=L_all ∩ Q`, with
   `L_all={a^n ξ b^n | n≥0, ξ∈{c,d,e}}`.
   Its Clark--Eyraud substitutability and preservation of linearity
   under regular intersection give the unnumbered general claim
   `L∈C_lin(h) => L∩g⁻¹(F)∈C_lin(h×g)`.
   This is not automatically covered by the existing CFG regular
   filtering proof: **linearity** is additional.
3. The preliminaries distinguish **set-based** polynomial
   characteristic-data guarantees for the batch operator
   from *incremental* polynomial time-and-data guarantees for the
   conservative sequential learner (not claimed here). The paper
   also adds Yoshinaka's non-identifiability observation for the
   **union** of fixed-window classes. Verify these scopes against
   the main Gold learner package; do not strengthen the result.
4. The linear-target characteristic-sample theorem explicitly
   bounds size polynomially in the given linear representation
   `|G|`; soundness emphasizes nonempty internal factors and
   an order-dependent final-hypothesis example is sharpened.
5. The nonlinear target cites Autebert--Berstel--Boasson directly
   for nonlinearity of `ΔΔ`. The source/typed thickness example
   remains a **presentation-specific** exponential gap,
   not a universal learning-data lower bound. Other edits adjust
   witnesses, attribution, and notation.

## Verification checkpoints and remaining work

- The complete fast/full CI for prior proof commit
  `7d6bf0ebe6d3657dbed04c2622935ac89aaae9ab`
  succeeded, including the recursor-based CFG least-closed bridge.
- New typed-thickness core work was added after that checkpoint.
  The subsequent `025244031bec243bf6ad6edb44eec619b766d0f6`
  checks failed on `V117TypedThicknessGapCore.lean` (simp,
  multiplication simplification, replicate rewriting).
  The newer Lean branch head at this audit is
  `43506b32781e8f4e5ff65e9e2b360683617955cb`;
  its CI was still in progress on inspection.
  **Do not count this branch as green without a completed run.**
- Work still required: full v118-specific proposition correspondence,
  rigorous direct semigroup proof mapping, linear regular-filter
  argument, exact executable v116 `O(n_K^4)` bound, completion of
  the *entire* `prop:typed-thickness-gap` (size, reduction,
  ordinary thickness, trimming), source-wide exact 31-claim audit,
  CFL inverse homomorphic-preimage representation, and final
  main-theorem algorithmic conjunction.
- `PAPER.yaml` expressly says `response/response_round1.tex`
  and clean/marked response package still reflect v117. Regenerate
  response text and page/line citations from the **v118** PDFs
  before submission. This source task is separate from Lean.
- Archived formal verification stays at **v88**, immutable tag
  `tcs1-v88-formalization-3.0.0` and DOI
  `10.5281/zenodo.23120560`. No v118
  formalization certificate, merged release, or DOI is claimed.

Working draft PR: https://github.com/growupkuriyama-hub/tcs1-lean-formalization/pull/7
