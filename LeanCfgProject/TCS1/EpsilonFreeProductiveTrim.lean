import LeanCfgProject.TCS1.UnitFreeProductiveTrim

/-!
# TCS #1 v69: concrete productive family after epsilon elimination

Proposition 7.4 first removes non-start epsilon rules and then deletes symbols
with no nonempty terminal yield before unit elimination.  Earlier facades kept
that surviving family abstract.  This module makes it concrete as a subtype.

Because EpsilonFreeDerives contains no epsilon constructor, productivity
already implies nonempty productivity.  The same subtype also receives every
productive state after unit elimination, using the exact language equivalence
proved by BinaryUnitElimination.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section EpsilonFreeProductiveTrim

variable {N : Type u}
variable {α : Type v}

/-- States having a terminal derivation after non-start epsilon elimination. -/
abbrev ProductiveEpsilonFreeState
    (G : BinaryNullableGrammar N α) :=
  {A : N // ∃ w, EpsilonFreeDerives G A w}

/-- Every retained epsilon-free state has a nonempty terminal yield. -/
theorem productiveEpsilonFree_allHaveNonempty
    (G : BinaryNullableGrammar N α) :
    AllHaveNonemptyYield
      (fun A : ProductiveEpsilonFreeState G =>
        {w | EpsilonFreeDerives G A.1 w}) := by
  intro A
  obtain ⟨w, hw⟩ := A.2
  exact ⟨w, hw, epsilonFreeDerives_nonempty G hw⟩

/--
Every state productive after unit elimination was already productive after
epsilon elimination.  This is the concrete embedding needed by the
epsilon/unit/trimming normalization facade.
-/
def productiveUnitFree_to_productiveEpsilonFree
    (G : BinaryNullableGrammar N α)
    (A : ProductiveUnitFreeState G) :
    ProductiveEpsilonFreeState G := by
  refine ⟨A.1, ?_⟩
  obtain ⟨w, hw⟩ := A.2
  exact ⟨w, unitFreeDerives_to_epsilonFree G hw⟩

@[simp] theorem productiveUnitFree_to_productiveEpsilonFree_val
    (G : BinaryNullableGrammar N α)
    (A : ProductiveUnitFreeState G) :
    (productiveUnitFree_to_productiveEpsilonFree G A).1 = A.1 :=
  rfl

end EpsilonFreeProductiveTrim

end TCS1
end LeanCfgProject
