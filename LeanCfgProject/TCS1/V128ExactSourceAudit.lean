import LeanCfgProject.TCS1.V126ExactSourceAudit
import LeanCfgProject.TCS1.V128SourcePrecisionAudit

/-!
# TCS #1 v128 exact-source audit

Frozen English source:
- Papers commit containing current main.tex: 3ad4aacda70de6208bf9f82de19518048f39dd51
- current baseline metadata commit: 92009e7c5e448499105a7dad67c03735dca6180d
- main.tex SHA-256:
  cb18358871d34f6120fed03bc9da7bfed5f1f3095487cca03b07d40ae4d90128

The complete v126 audit remains the inherited mathematical baseline.
The only post-v126 source-facing obligations added here are the v128 precision
claims: the exact long-word interpretation of distinct fixed-window type
equality, and separate empty-target handling by the empty sample.
-/

namespace LeanCfgProject
namespace TCS1

#check v126_exact_source_delta_audited
#check v128_fixedWindowThreshold_exact
#check v128_fixedWindow_type_eq_iff_long_of_ne
#check v128_batchLanguage_empty_sample
#check v128_empty_target_handled_by_empty_sample

theorem v128_exact_source_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
