# TCS #1 v126 complete Lean reverification ledger

Status: **IN PROGRESS — do not claim complete manuscript verification yet.**

This ledger intentionally audits more than theorem environments.  The previous
delta audit was useful but could miss mathematically substantive prose.  For
v126, completion requires both the numbered theorem surface **and** the
unnumbered proof-critical claim surface to be accounted for.

## Frozen manuscript source

English source of truth:

- repository: `growupkuriyama-hub/Papers`
- repository HEAD used for the freeze:
  `cb3097eb58e38743172ace7965360a64dcfc10ef`
- file: `01_fixed-h-cfg/main.tex`
- last commit changing that English source:
  `0e774ef6e50d874535d963ad8cad804b213534b5`
- file blob SHA:
  `f79fed0f37aba7c5c8994e6d8bce55d3214ff54e`
- SHA-256 recorded by `PAPER.yaml`:
  `0dd9cb51c1b2f7aed0863b3a6d6f3a448cde6320a776af13d2240f010aed7a4c`
- internal paper version: **v126**
- theorem/proposition/lemma/corollary environments: **30**

Lean work branch:

- `tcs1-v126-complete-reverification`
- forked from the latest `tcs1-v123-reverification` work branch.
- The branch is not to be merged/tagged as a verified release until every
  non-external item below is green and every external item is explicitly
  identified as literature input.

## Status vocabulary

- **Internal**: a statement matching the manuscript claim is proved in Lean.
- **Inherited**: exact mathematical claim is already covered by the archived
  theorem-facing Lean development and is unchanged in v126.
- **Bridged**: the changed v126 representation is connected by a proved
  equivalence/transport theorem to an inherited verified statement.
- **External**: the manuscript deliberately cites a literature theorem; the
  dependency is explicit and no claim is made that Lean reproves it.
- **Partial**: some but not all clauses are internally covered.
- **Open**: a manuscript claim still lacks an adequate Lean proof or explicit
  external-theorem boundary.
- **Source defect**: the prose has a binding/statement problem even if the
  intended mathematical fact is otherwise verified.

## A. Complete numbered theorem surface (30 environments)

| # | Manuscript claim | Lean evidence | v126 status |
|---|---|---|---|
| 1 | `prop:regular-auto` | `regular_auto_proposition_package`, `regular_exists_fixedHSubstitutable` | Inherited/Internal |
| 2 | `prop:finite-info-closure` | `V121FiniteInformationClosure`: product intersection, recognized filter, erasing inverse image | **Partial**: distributional/fixed-h core Internal; standard CFL closure under regular intersection and inverse homomorphism remains External |
| 3 | `prop:yl-special` | `fixedWindowSubstitutable_iff_fixedHSubstitutable` and concrete window monoid | Inherited/Internal |
| 4 | `thm:main` five clauses | archived main-theorem packages + post-v88 bridges | **Partial until rows 5, 12, 15, 19 and full CI close** |
| 5 | `prop:li-window` | `V121LocallyTrivialBridge`; `V126LocallyTrivialCore`; `V126FixedWindowPositiveLocalTrivial` | **Partial/External**: elementary sandwich and fixed-window positive-image local triviality are Candidate Internal; finite-semigroup decomposition and reverse kernel-refinement implication still require explicit treatment |
| 6 | `lem:sample-consistency` | `sample_consistency`, `substring_sample_consistency` | Bridged/Internal |
| 7 | `thm:soundness` | `batchLanguage_sound`, `substring_batchLanguage_sound` | Bridged/Internal |
| 8 | `prop:typed-core` exact retained fibre equality | `V123TypedFiberEquality` | Candidate Internal; must pass v126 CI |
| 9 | `thm:complete` | canonical witness completeness + substring quotient bridge | Bridged/Internal |
| 10 | `thm:reconstruction-fixed-h` | exact reconstruction packages + substring quotient equality | Bridged/Internal |
| 11 | `cor:ilt` | indexed/concrete/materialized conservative Gold packages | Bridged/Internal |
| 12 | `thm:poly-build` | archived candidate-space bounds + `V121SubstringCost` | **Partial**: distinct-state O(n²) and bucket cubic inequality are represented; exact v126 quotient constructor/output-writing O(n⁴) correspondence still to close |
| 13 | `lem:typed-thickness-bound` | typed witness/context bound modules | Inherited/Internal |
| 14 | `cor:typed-thickness-data` | typed-thickness characteristic package | Inherited/Internal |
| 15 | `prop:typed-thickness-gap` | `V121TypedGapKernel`, `V121TypedGapGrammar` | **Partial pending CI and remaining packaging**: exact E_i exponential typed yield and concrete grammar/trim work exist; full O(n), reducedness, full source thickness/language and final tau statement must be checked as one package |
| 16 | `lem:window-typed-yield` | fixed-window reduced minimal-yield bounds | Inherited/Internal |
| 17 | `thm:window-thick` | concrete fixed-window Section 7 package | Inherited/Internal |
| 18 | `prop:thick-ssbnf-normal` | Proposition 7.4 indexed package + trim audit | Inherited/Internal; v124 rewrote prose proof but not theorem statement |
| 19 | `cor:li-thickness` | `characteristicPackage_of_positiveWindowKernelRefinement` | **Conditional/Internal + External algebra input**: learning bridge Internal; deriving the refinement from local triviality is row 5 |
| 20 | `prop:linear-normal` | indexed linear normalization theorem/language/size packages | Inherited/Internal; v124 Appendix rewrite must be checked only for statement consistency |
| 21 | `lem:linear-short` | linear canonical-yield/spine bounds | Inherited/Internal |
| 22 | `thm:linear-poly` | indexed linear characteristic package | Inherited/Internal |
| 23 | `prop:linear-separator-example` | `lpm_proposition86_full_semantic` | Inherited/Internal |
| 24 | `prop:nonlinear-rs-example` | `DeltaStar.nonlinear_rs_example_full` | **Partial**: CFG, nonregularity, nonlinearity, fixed-h and non-window clauses Internal; manuscript adjective **deterministic context-free** still needs a concrete DPDA/certified deterministic recognizer or an explicit external boundary |
| 25 | `thm:ctr-non-kl` | capped-counter fixed-window theorem | Inherited/Internal |
| 26 | `lem:finite-monoid-obstruction` | finite monoid obstruction kernel | Inherited/Internal |
| 27 | unlabelled uncapped-counter corollary | uncapped counter obstruction | Inherited/Internal |
| 28 | `cor:dyck-not-rs` | one-bracket Dyck obstruction | Inherited/Internal |
| 29 | `lem:rs-fixed-quotient` | fixed-H right quotient | Inherited/Internal |
| 30 | `prop:clark-congruential-comparison` | Clark congruential packages; relies on typed-core exactness | Inherited plus v123 fibre bridge; final status waits for row 8 CI |

## B. Unnumbered proof-critical claim surface

These entries are mandatory for this audit.  They are not allowed to disappear
merely because a raw LaTeX theorem-environment count does not see them.

| ID | v126 prose/math claim | Evidence / obligation | Status |
|---|---|---|---|
| U1 | typing refinement is monotone on positive factors | generic refinement theorem in `FixedHSubstitutability` | Internal |
| U2 | `ker(h×g)=ker h ∩ ker g`; either component class embeds in product typing | `FixedHTypingRefinement` | Internal |
| U3 | RS and RS∩CFL contain all finite languages and Sigma*; Gold then makes the unions nonlearnable | regular-language package proves inclusion; Gold superfinite theorem is classical learning-theory input | Internal + External |
| U4 | Yoshinaka's L0 is an existing fixed-window counterexample | literature attribution, not a new theorem of this paper | External/citation |
| U5 | finite fixed-h class omits a finite language; manuscript uses `{x,y,zx}` | `GoldCompatibilityFiniteObstruction.fixedH_omits_some_finite_language` | Internal; **source text currently leaves z syntactically unbound at lines 530–532** |
| U6 | locally trivial definition `ete=e` implies `etf=ef` for idempotent e,f | `V126LocallyTrivialCore.locallyTrivial_between_idempotents` | Internal, new v126 |
| U7 | the manuscript sandwich collapse `a e (b s c) f d = a e f d` | `V126LocallyTrivialCore.locallyTrivial_double_sandwich` | Internal, new v126 |
| U8 | finite-semigroup factorization `S^n=SE(S)S` for the chosen n | Pin II.6.35 in paper; no project axiom | **External unless internally reproved later** |
| U9 | non-local-triviality supplies the fixed-window collision construction used in reverse implication of Prop. li-window | `V126NonLocalTrivialWindowObstruction.nonLocalTrivial_obstructs_every_fixedWindow` | Candidate Internal; CI required |
| U10 | positive image of each concrete window monoid is locally trivial | `V126FixedWindowPositiveLocalTrivial.fixedWindow_positive_image_locally_trivial` | Candidate Internal; CI required |
| U11 | one substring nonterminal per distinct observed nonempty factor is extensionally equivalent to archived occurrence indexing | `V121SubstringReconstruction` | Bridged/Internal |
| U12 | O(n²) distinct substring state upper bound | `V121SubstringCost.v121_factorCandidates_card_le_sq` | Candidate Internal; CI required |
| U13 | unary context/type bucket square-sum gives cubic emission bound | `V121SubstringCost.v121_bucket_emissions_le_cube` | Candidate Internal; exact concrete bucket enumerator still to connect |
| U14 | literal production output gives O(n⁴) grammar construction | exact executable quotient/output-size correspondence still missing | Open/row 12 |
| U15 | typed gap E_i type-one yields have length exactly 2^i | `V121TypedGapKernel` | Candidate Internal; CI required |
| U16 | actual G_n^c retains (E_n,1) after productive/reachable typed trim | `V121TypedGapGrammar.gap_eTop_retained` | Candidate Internal; CI required |
| U17 | every source non-start symbol in G_n^c has a unit-length yield | `V121TypedGapGrammar.gap_source_has_unit_yield` | Candidate Internal; full source/start thickness packaging still needed |
| U18 | v126 unnumbered linear regular-filter implication `L∈Clin_h, Q=g^{-1}(F) => L∩Q∈Clin_{h×g}` | `V126LinearRegularFilterClosure.rawLinear_fixedH_inter_recognized_product` | Candidate Internal; CI required |
| U19 | specific `L_all` is Clark–Eyraud substitutable | no exact dedicated theorem mapped yet | Open |
| U20 | specific identity `L_{±,e}=L_all∩Q` and regularity of Q | no exact dedicated theorem mapped yet | Open |
| U21 | production-label set `C_{h,F}(G)` is regular with the stated V×M×M automaton | no exact theorem mapped yet | Open |
| U22 | CTR_rho is regular and transition monoid recognizes it | `CappedCounterFiniteState` | Internal |
| U23 | sharp prose boundary CTR_1 is (1,1)-substitutable | `V121CappedCounterOne.fixedWindowSubstitutable_one` | Candidate Internal; CI required |
| U24 | uncapped CTR is deterministic context-free via counter-with-reset | RS obstruction Internal; deterministic-PDA classification itself not currently mapped | Open/external-boundary decision required |
| U25 | D1 is deterministic context-free | paper cites classical source; RS obstruction Internal | External classification + Internal obstruction |
| U26 | Lukasiewicz identity `L_Luk=D1 b` and quotient implication to not-RS | Lukasiewicz/Dyck boundary modules + right quotient | Inherited/Internal for the manuscript consequence; cited DCFL classification remains External |
| U27 | Delta-star displayed CFG and exact intersection with four-block regular language | DeltaStar grammar/intersection modules | Internal |
| U28 | Delta-star deterministic context-free parser claim | exact DPDA object/correctness not mapped | Open/row 24 |
| U29 | linear languages closed under regular intersection | `LinearRegularIntersection` proves this for repository raw finite linear presentations | Internal |
| U30 | main theorem conclusion prose about no incremental polynomial-data guarantee | statement discipline, not an extra mathematical theorem; audit against EHY definitions separately | Source-scope check |
| U31 | control-set discussion makes no equivalence/subsumption claim | scope disclaimer; regularity claim is U21 | Source-scope check |
| U32 | typed-thickness gap limits this refinement analysis, not all possible learning algorithms | scope disclaimer; does not create a stronger lower-bound theorem | Source-scope check |
| U33 | background characterization: linear languages are exactly one-turn pushdown languages | cited Ginsburg--Spanier / Autebert background, not a new paper result | External/citation |
| U34 | Delta-star balance/zero-height characterization marked `(star)` | exact parser/Kleene-star semantics is Internal, but the displayed balance/ba iff itself is not yet statement-matched | Open |
| U35 | finite boundary summary `h_star` carries the concatenation monoid and is a homomorphism | `DeltaStarTyping.starTypeMonoid`, `starSummary_append`, `starTyping` | Internal |
| U36 | the four-element `h_{±,e}` has the stated center-count behavior | `LinearSeparatorTyping` and fixed-H separator package | Internal; exact prose behavior to cross-check |
| U37 | standard doubling grammar has O(n) presentation and singleton language `{a^(2^n)}` | `DoublingSingletonGrammar` | Internal/inherited |


## C. New v123–v126 mathematical deltas that must not be hidden by “inherited”

1. **Typed fibre equality** in Proposition `prop:typed-core` is stronger than
   the old yield-type-only statement.  It is tracked by
   `V123TypedFiberEquality`.
2. **Locally trivial positive-image proof** now uses
   `n=|h(Sigma+)|+1`, the cited finite-semigroup decomposition, and the
   idempotent sandwich collapse.  The elementary sandwich part is now internal
   in `V126LocallyTrivialCore`; the remaining algebraic theorem boundary is
   visible in U8–U10 rather than hidden under a citation.
3. **Linear regular-filter closure** is a displayed but unnumbered claim in the
   current linear example.  It is tracked by
   `V126LinearRegularFilterClosure`.
4. **Typed-thickness exponential example** is a concrete grammar claim, not
   merely the numerical E_i recurrence.  The audit will not mark it complete
   until grammar size, reducedness, source thickness, trim survival and the
   final typed-thickness inequality are packaged together.
5. **DCFL adjectives** are audited separately from CFG/CFL facts.  A
   deterministic prose parser is not automatically a Lean DPDA theorem.

## D. Completion gate

The phrase **“v126 manuscript Lean verification complete”** is forbidden until:

1. all 30 rows in section A are Internal/Inherited/Bridged, or explicitly
   External for a cited theorem;
2. every U-entry that is a paper-owned mathematical assertion is Internal,
   Bridged, or deliberately rewritten/cited as External;
3. no Open or unexplained Partial item remains;
4. `LeanCfgProject.TCS1.All` builds on the exact v126 branch head;
5. the focused v126 post-v88 delta workflow builds and rejects proof
   placeholders/project axioms;
6. an exact-source audit file imports/checks every mapped v126 claim;
7. the manuscript source has not changed since the frozen commit, or the audit
   is rerun against the new exact source.

A green CI by itself proves only that the formalized files compile.  It does
not prove that manuscript coverage is complete.
