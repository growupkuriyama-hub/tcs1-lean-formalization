# TCS #1 v117 — ongoing Lean re-verification (NOT a certificate)

Date: 2026-10-07. **Draft verification ledger.**
Authoritative article: `growupkuriyama-hub/Papers/01_fixed-h-cfg/main.tex`,
internal **v117**, article commit `33220b2ed701490acf5d43799788cff5cff4abd7`,
source SHA-256 `b384bcbb57fb4473a4f9a0f3cd135d90f3aa83c8a78b22a92920a31fed889524`.
This is a working major revision, **not** asserted to have been submitted.

## Verified earlier checkpoint

The immutable Lean `tcs1-v88-formalization-3.0.0` archive and
DOI `10.5281/zenodo.23120560` cover the **v88** theorem-facing
baseline only. This branch inherits that layer without changing the
archived release.

## Claim count and paper delta

The current v117 manuscript has **31**
`theorem`/`lemma`/`proposition`/`corollary` environments,
versus **30** in the existing `V115TheoremSurfaceAudit.lean` crosswalk.
The additional statement is
`prop:typed-thickness-gap`: a family of reduced SSBNF grammars
of linear size with ordinary thickness one but exponentially large
type-refined thickness, for a fixed two-element monoid. This is
**not** an algorithm-independent characteristic-data lower bound.

The v116/v117 finite-sample grammar is **substring indexed**
(`[x]` instead of `[x:u,v]`), with branching (B), shared-context
equal-type unary (U), lexical (L), and separate sample/epsilon start
(S). v117 does not modify the v116 theorem statements or learning
constructor, but citation and proof-presentation updates require
the usual verification provenance audit.

## New bridge

`LeanCfgProject/TCS1/V116SubstringQuotient.lean` represents the
new B/U/L/S derivations and states:

* `v116_old_to_new` maps old R1–R4 derivations to new derivations
  (old context-transport R2 maps to zero steps).
* `v116_new_to_old` simulates any new derivation from **every**
  observed old representative, transporting context before each
  U or B step.
* `v116_batchLanguage_eq_v115` establishes exact extensional
  generated-language equality **for all finite samples**, including
  the epsilon start convention.

**Do not count these new claims as machine checked until the relevant
Lean CI is green.** In particular a green `All` build is required
after code changes.

## Outstanding obligations (not claimed proved)

1. Confirm green latest CI for the quotient and the fixes to
   `GeneralCFGDerivationBridge` and `V115InverseHomReduction`.
2. Align the finite-state *executable* hypothesis and explicit
   complexity proof to v116's substring states, particularly the
   new **O(n_K^4)** encoding/construction bound. The old
   `reconstructionOutputEncodingEnvelope_le_degreeFive`
   checks the v115 presentation instead.
3. Formalize/audit `prop:typed-thickness-gap` explicitly, including
   grammar reducedness, ordinary thickness, survival of typed `(E_n)_1`
   after trimming, and shortest typed yield length `2^n`.
4. Finish the current source-facing claim crosswalk; `#check` alone
   is never an exact-statement proof certificate.
5. The v115 draft PR explicitly left open an exhaustive CFG
   inverse-homomorphic-preimage construction (Proposition 3.2(iii)),
   and full exact conjunction/algorithmic aspects of the main learning
   theorem. Preserve this scope distinction until each proof is built.
6. Only after all obligations and full CI pass can a separate exact
   v117 versioned release and DOI be considered.

Current working PR: `tcs1-lean-formalization#7` (draft), not merged.
