# TCS #1 v128 strict reproduction audit

Status: **SOURCE-SYNCHRONIZED AND CI-GREEN, WITH EXPLICIT NON-INTERNAL BOUNDARIES.**

This document answers the stronger question:

> Is every mathematical and algorithmic assertion in the current v128
> manuscript reproduced *inside Lean itself*, rather than merely synchronized
> with Lean proofs plus cited background theorems and conventional complexity
> reasoning?

The answer is **no in that strongest sense**.  The paper-owned semantic core is
very extensively formalized, but a small set of literature inputs and
machine-cost claims remain deliberately outside the internal Lean kernel.

## Exact source freeze

Current English manuscript:

- paper repository: `growupkuriyama-hub/Papers`
- current paper repository HEAD checked during this audit:
  `95b87182d8d3b46b84f27b0be7cd386ea55bbb42`
- last commit changing `01_fixed-h-cfg/main.tex`:
  `3ad4aacda70de6208bf9f82de19518048f39dd51`
- current `main.tex` blob:
  `e503bfc7b86c963d7ff3b52c3158b06ea9c10c6f`
- current SHA-256:
  `cb18358871d34f6120fed03bc9da7bfed5f1f3095487cca03b07d40ae4d90128`
- `PAPER.yaml` baseline: **v128**, with exactly the same SHA-256
- theorem/proposition/lemma/corollary environments: **30**
- current paper LaTeX CI on repository HEAD: **success**

Lean checkpoint:

- branch: `tcs1-v128-complete-reverification`
- exact-source aggregate: `V128ExactSourceAudit.lean`
- full facade CI: **success**
- v128 exact-source CI: **success**
- repository TCS1 no-`sorry` / no project-`axiom` gate: **success**

## Strict classification of the 30 numbered statements

Legend:

- **I** = the manuscript-owned mathematical content is internally represented
  by Lean proof terms.
- **E** = an explicitly cited/background theorem is intentionally imported as
  a mathematical boundary rather than reproved.
- **C** = the combinatorial/executable ingredients are formalized, but the
  literal asymptotic running-time wording is not interpreted in a fully
  formal machine-cost semantics.
- **M** = mixed: the theorem combines internal statements with E and/or C.

| # | Manuscript statement | Strict status | Reason |
|---|---|---|---|
| 1 | `prop:regular-auto` | I | finite-monoid recognition and fixed-h substitutability package |
| 2 | `prop:finite-info-closure` | M = I+E | fixed-h/product/erasing-type logic internal; standard CFL closure under regular intersection and inverse homomorphism external |
| 3 | `prop:yl-special` | I | concrete tagged fixed-window monoid and exact substitutability equivalence |
| 4 | `thm:main` | M = I+E+C | semantic learning clauses internal; locally-trivial clause uses Pin input; batch polynomial-time wording inherits the cost-model boundary below |
| 5 | `prop:li-window` | M = I+E | all paper-specific implications/unions internal after Pin's finite-semigroup factorization; factorization itself external |
| 6 | `lem:sample-consistency` | I | exact |
| 7 | `thm:soundness` | I | exact |
| 8 | `prop:typed-core` | I | exact retained type-fibre equality |
| 9 | `thm:complete` | I | exact witness completeness |
| 10 | `thm:reconstruction-fixed-h` | I | exact reconstruction |
| 11 | `cor:ilt` | I | concrete/executable conservative Gold convergence and at-most-one-change form |
| 12 | `thm:poly-build` | C | finite candidate spaces, explicit tables, output envelopes and executable membership machinery are internal; no low-level machine/step semantics proves the literal phrase "time polynomial" for the whole constructor |
| 13 | `lem:typed-thickness-bound` | I | explicit witness/context bounds |
| 14 | `cor:typed-thickness-data` | I | exact characteristic-sample and encoded-size bound |
| 15 | `prop:typed-thickness-gap` | I | concrete family, source language, reducedness/reachability, source thickness, linear presentation count, and exponential typed lower witness |
| 16 | `lem:window-typed-yield` | I | exact fixed-window yield bound |
| 17 | `thm:window-thick` | I | explicit polynomial characteristic-data envelope |
| 18 | `prop:thick-ssbnf-normal` | M = I+C | language/thickness/size transformation package internal; literal polynomial-time conversion is not equipped with a machine-cost semantics |
| 19 | `cor:li-thickness` | M = I+E | learning/size bridge internal, Pin factorization external |
| 20 | `prop:linear-normal` | M = I+C | semantic normalization, shape and source-polynomial size internal; an intermediate prepared grammar is noncomputable/classically chosen and no operational polynomial-time cost theorem is supplied |
| 21 | `lem:linear-short` | I | exact |
| 22 | `thm:linear-poly` | I | exact polynomial characteristic-sample size claim |
| 23 | `prop:linear-separator-example` | I | linearity, nonregularity, fixed-h substitutability and all non-window/non-Clark clauses internal |
| 24 | `prop:nonlinear-rs-example` | M = I+E | CFG/nonregular/nonlinear/fixed-h/non-window clauses internal; "deterministic context-free" is not represented by a project DPDA object |
| 25 | `thm:ctr-non-kl` | I | exact |
| 26 | `lem:finite-monoid-obstruction` | I | exact |
| 27 | uncapped-counter corollary | I | exact RS obstruction |
| 28 | `cor:dyck-not-rs` | I | exact RS obstruction |
| 29 | `lem:rs-fixed-quotient` | I | exact |
| 30 | `prop:clark-congruential-comparison` | I | containment/properness package internal |

Thus, at the theorem-environment level, **22/30 are fully internal under the
strict criterion above**.  The remaining eight are not mathematical holes:
they are mixed with explicit literature inputs or with an operational
complexity-model boundary.

## v128-specific source changes

The final reviewer-facing v128 changes were independently checked.

### Fixed-window unary-rule clarification — internal

The manuscript now says that for **distinct observed nonempty factors**,
equality of concrete `h_{k,l}` type is equivalent to the long-word case:
both lengths are at least

`max {1, k+l}`

and the length-`k` prefixes and length-`l` suffixes agree.

This is exactly:

- `v128_fixedWindowThreshold_exact`
- `v128_fixedWindow_type_eq_iff_long_of_ne`

in `V128SourcePrecisionAudit.lean`.

### Empty target — internal

The manuscript now scopes the locally-trivial characteristic-data statements
to nonempty targets and says the empty target is handled separately.

This is exactly:

- `v128_batchLanguage_empty_sample`
- `v128_empty_target_handled_by_empty_sample`

in `V128SourcePrecisionAudit.lean`.

### Pin exponent — source checked

The manuscript uses

`n = |h(Sigma+)| + 1`

and invokes the finite-semigroup factorization `S^n = S E(S) S`.
The checked Pin reference states Corollary II.6.35 for **every**
`n > |S|`, so the manuscript's `|S|+1` is exactly within the cited range.
This is not an off-by-one error.

Every manuscript-specific consequence after that factorization is internal in
`V126PinFactorizationBridge.lean`.

## Unnumbered mathematical claims

The earlier U1--U37 audit was rerun against the current v128 source.  The final
source adds no untracked paper-owned semantic theorem.

Important statuses:

- one nonterminal per distinct observed nonempty factor: internal;
- exact fixed-window long-word interpretation: internal (new v128 theorem);
- empty target / empty sample: internal (new v128 theorem);
- polynomial conservative-update *work envelope*: internal and attached to the
  actual executable factor-slot/CYK learner;
- control-set regularity and the equality
  `L(G,C_{h,F}(G)) = L(G) intersect h^{-1}(F)`: internal;
- exact Delta-star balance/zero-height iff: internal;
- capped-counter regularity and transition-monoid recognition: internal;
- `L_all` Clark--Eyraud substitutability and the parity-filter identity:
  internal.

The following remain external or representation-level boundaries:

1. **Pin Corollary II.6.35**: finite-semigroup factorization.
2. **Gold's classical superfinite obstruction**.
3. **standard CFL closure** under regular intersection and inverse
   homomorphism.
4. **Yoshinaka's published fixed-window counterexample** `L0`.
5. **DCFL classifications** for the uncapped counter, `D1`, and Delta-star.
   Delta-star's paper-specific deterministic scanner and exact language
   semantics are nevertheless internal.
6. **linear = one-turn PDA** background characterization.
7. **regularity of the displayed parity filter Q** is used as the standard
   regular-expression fact; the exact intersection identity with
   `L_{±,e}` is internal, but no dedicated DFA proof of Q's regularity is
   currently needed/packaged.
8. **machine-cost interpretation of asymptotic construction time**:
   operation/count envelopes are formalized, including executable CYK and
   conservative updates, but the repository does not define a universal
   RAM/Turing-machine cost semantics for every constructor and normalization.
9. the prose comparison saying the fixed-window constructor agrees with
   Yoshinaka's published algorithm "up to redundant identity rules, start
   representation, and lambda handling" is a source-comparison claim, not a
   formal theorem relating two mechanized implementations of Yoshinaka's
   external algorithm.

## Algorithmic claims: what is and is not reproduced

The repository goes substantially beyond a purely semantic formalization:

- finite reconstruction candidate spaces are concrete Fintypes;
- production relations are decidable;
- materialized production tables exist;
- unit closure is finite and executable;
- reconstructed-language membership has a Boolean CYK procedure with exact
  correctness;
- the conservative learner has an executable update function;
- a single explicit polynomial work envelope bounds unit closure + CYK +
  possible rebuild along the actual executable learner.

Therefore the update-side polynomial claim is strongly mechanized.

The weaker point is specifically the literal phrase **"constructible /
converted in polynomial time"** for whole grammar constructors and
normalizations: the Lean development proves explicit polynomial sizes and
enumeration/work envelopes, but does not attach a formal step-count semantics
to every constructor.  In particular, the linear-normalization pipeline uses a
`noncomputable` prepared-grammar choice internally, even though its semantic
and polynomial-size theorem is proved.

## Bottom line

Two different completeness statements must not be conflated:

1. **Exact manuscript synchronization, relative to explicit literature and
   representation/cost boundaries:** COMPLETE and CI-green.
2. **Everything in the prose, including every cited theorem and every
   asymptotic runtime phrase, reproved in a single self-contained Lean machine
   model:** NOT COMPLETE.

No unaccounted contradiction or theorem-strength mismatch was found in the
current v128 source.  The remaining boundaries are now listed explicitly
rather than being hidden under the word "complete".
