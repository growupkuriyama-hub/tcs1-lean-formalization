# TCS #1 v87 Lean formalization — release 2.0.0

This release archives the Lean theorem-facing verification synchronized to
internal manuscript **v87** of:

> Takayuki Kuriyama, *Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing*.

## Exact manuscript baseline

- paper repository: `growupkuriyama-hub/Papers`
- manuscript source: `01_fixed-h-cfg/main.tex`
- internal manuscript version: **v87**
- last commit changing the manuscript source:
  `9377366545e48a405a6f59ea5cda3b02096166ac`
- manuscript SHA-256:
  `efa8d3eb321e82d7d5c72d4f4fd8d6c7077b4051ac456309349118472ddeeb96`

## Verification checkpoint

- v87 exact synchronization merge:
  `cefe7e904fc1e16174761b726008363666fe8b71`
- TCS1 Lean CI run #308: success
- theorem-facing critical path: success
- full `LeanCfgProject.TCS1.All`: success
- no placeholder proofs in the TCS1 Lean source tree
- no project-level axiom declarations in the TCS1 Lean source tree

## v87 synchronization result

A direct v86-to-v87 source comparison found 34
theorem/proposition/lemma/corollary environments in each version and no changes
to any of those environment contents.  The v87 manuscript changes are
proof-exposition clarifications only.

The v87 audit rechecks the formal declarations corresponding to the edited
proof regions, including:

- explicit ordinary-thickness witnesses and reducedness for the indexed
  `R_n` and `R_n^-` grammars;
- literal clean-node-body occurrence recognition;
- replay admissibility of shortcut/clean body toggles;
- the residual-height difference-core theorem;
- the complete level-coded Appendix substitutability theorem; and
- the aggregate indexed ordinary-thickness lower-bound package with the
  exponential characteristic-sample norm lower bound.

See `FORMALIZATION_TCS1_V87.md` and
`LeanCfgProject/TCS1/V87FullManuscriptAudit.lean` for the exact synchronization
record.

## Scope

This is a theorem-facing verification artifact.  It does not claim that every
sentence, citation, exposition choice, or formatting decision in the article
has been formalized.

## Build

```bash
lake build LeanCfgProject.TCS1.All
```

Release tag: `tcs1-v87-formalization-2.0.0`.  Zenodo DOI: `10.5281/zenodo.23114558`.
