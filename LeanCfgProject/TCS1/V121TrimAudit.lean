import LeanCfgProject.TCS1.UnitFreeReachableTrim
import LeanCfgProject.TCS1.ConcreteTypedTrimming

/-!
# TCS #1 v121: trim-definition audit

The v121 manuscript corrects the prose definition of CFG trim to the standard
two-stage construction:

1. delete nonproductive symbols first;
2. compute reachability in the remaining productive grammar and delete the
   unreachable symbols.

This order is already the order implemented by the archived Lean normalization
pipeline.  This file records that correspondence explicitly, rather than
introducing a new normalization algorithm.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V121TrimAudit

variable {N : Type u}
variable {α : Type v}

/-- The final productive-then-reachable trim preserves the designated start
language exactly. -/
theorem v121_trim_start_language_preserved
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G)
    (w : List α) :
    BinaryNullableDerives
        (reducedUnitFreeGrammar G start)
        (reducedUnitFreeStart G start) w
      ↔
    UnitFreeDerives G start.1 w :=
  reducedStart_language_iff_unitFree G start w

/-- Every symbol retained after the two-stage trim is productive. -/
theorem v121_trim_retained_productive
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G) :
    ∀ A : ReducedUnitFreeState G start,
      ∃ w,
        BinaryNullableDerives
          (reducedUnitFreeGrammar G start) A w :=
  reducedUnitFreeGrammar_all_productive G start

/-- Every symbol retained after the two-stage trim is reachable in the
productive grammar. -/
theorem v121_trim_retained_reachable
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G)
    (A : ReducedUnitFreeState G start) :
    ProductiveUnitFreeReachable G start A.1 :=
  reducedUnitFreeGrammar_all_reachable G start A

end V121TrimAudit

end TCS1
end LeanCfgProject
