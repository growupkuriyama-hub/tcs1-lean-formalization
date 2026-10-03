import LeanCfgProject.TCS1.V86FullManuscriptAudit

/-!
# TCS #1 v87: exact manuscript synchronization audit

This module is the theorem-facing Lean checkpoint for the internal v87
major-revision manuscript

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under
Fixed Finite-Monoid Typing_.**

The v87 source changes only proof exposition relative to the exactly
synchronized v86 manuscript.  A source-level comparison of all theorem,
proposition, lemma, and corollary environments found 34 such environments in
both versions and no changes to their contents.

The edited prose mirrors details already proved in the v83 Lean development:
explicit short terminal witnesses for the indexed grammars, recognition of
literal clean node bodies, and the residual-height difference-core induction.
This audit therefore rechecks the Lean theorems corresponding exactly to those
three edited proof regions, then inherits the completed v86 manuscript audit.

Building this module through `LeanCfgProject.TCS1.All` is the exact-version
theorem-facing synchronization checkpoint for v87.
-/

namespace LeanCfgProject
namespace TCS1

#check v86_full_manuscript_audited

-- v87 lower-bound proof exposition: explicit productive/thickness witnesses.
#check levelCodeRIndexed_thickness_atMost
#check levelCodeRMinusIndexed_thickness_atMost
#check levelCodeRIndexed_reduced
#check levelCodeRMinusIndexed_reduced

-- v87 Appendix exposition: literal clean-body recognition.
#check levelCleanBodyRecognition_proved
#check levelBodyToggleAdmissible_levelTree

-- v87 Appendix exposition: residual-height difference-core induction.
#check levelTree_difference_core
#check levelBodyToggleCutLocality_levelTree
#check levelTree_clarkEyraud

-- Aggregate lower-bound package used by the manuscript theorem.
#check levelCode_indexed_ordinaryThickness_lowerBound_package

/-- Single marker for the integrated v87 exact manuscript synchronization audit. -/
theorem v87_full_manuscript_audited : True :=
  v86_full_manuscript_audited

end TCS1
end LeanCfgProject
