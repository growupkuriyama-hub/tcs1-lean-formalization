import LeanCfgProject.TCS1.V79PreliminariesAudit
import LeanCfgProject.TCS1.V79ManuscriptClaimAudit
import LeanCfgProject.TCS1.V79FrontBackAppendixAudit

/-!
# TCS #1 v79: full manuscript audit facade

This is the manuscript-order integration point for the current v79 working
source.

The three component audits cover:
* Section 2 preliminaries and learning-model conventions;
* every numbered theorem/lemma/proposition/corollary in Sections 3--9,
  together with selected unnumbered mathematical claims; and
* the Abstract, Introduction contribution list, Conclusion summary, and
  Appendices A--C.

The audit deliberately distinguishes internally verified mathematics from
two kinds of statements that are not Lean proof obligations here:
standard literature background explicitly cited by the manuscript, and open
problems stated as open.

Building this module therefore gives one compile-time checkpoint for the
paper-facing Lean coverage of the v79 manuscript.
-/

namespace LeanCfgProject
namespace TCS1

#check v79_preliminaries_claims_audited
#check v79_numbered_manuscript_claims_audited
#check v79_front_back_appendix_claims_audited

/-- Single marker for the integrated v79 manuscript audit. -/
theorem v79_full_manuscript_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
