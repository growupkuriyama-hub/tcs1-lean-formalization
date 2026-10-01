import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v83: generic set-driven characteristic-sample obstruction

This module isolates the operator-independent lemma introduced in the v83
ordinary-thickness lower-bound section.  It is deliberately independent of
the concrete batch learner: only the usual set-driven characteristic-sample
contract is used.
-/

namespace LeanCfgProject
namespace TCS1

universe u

/--
A finite positive set C is characteristic for a set-driven language operator B
and target L when every finite positive supersample of C is reconstructed
exactly as L.
-/
def IsSetDrivenCharacteristicSample
    {α : Type u}
    (B : Finset (Word α) → Set (Word α))
    (L : Set (Word α))
    (C : Finset (Word α)) : Prop :=
  (↑C : Set (Word α)) ⊆ L ∧
  ∀ K : Finset (Word α),
    C ⊆ K →
    (↑K : Set (Word α)) ⊆ L →
    B K = L

/--
Nested-target obstruction from the v83 manuscript.

If L' is a proper sublanguage of L and the same set-driven operator has
characteristic samples C and C' for the two targets, then C must contain a
word from L \ L'.
-/
theorem nestedTarget_characteristicSample_obstruction
    {α : Type u}
    [DecidableEq α]
    (B : Finset (Word α) → Set (Word α))
    {L' L : Set (Word α)}
    (hsub : L' ⊆ L)
    (hne : L' ≠ L)
    {C C' : Finset (Word α)}
    (hC : IsSetDrivenCharacteristicSample B L C)
    (hC' : IsSetDrivenCharacteristicSample B L' C') :
    ((↑C : Set (Word α)) ∩ (L \ L')).Nonempty := by
  by_contra hnone
  have hCsub : (↑C : Set (Word α)) ⊆ L' := by
    intro w hwC
    by_contra hwNot
    apply hnone
    exact ⟨w, hwC, hC.1 hwC, hwNot⟩

  let K : Finset (Word α) := C ∪ C'

  have hCK : C ⊆ K := by
    intro w hw
    exact Finset.mem_union_left C' hw

  have hC'K : C' ⊆ K := by
    intro w hw
    exact Finset.mem_union_right C hw

  have hKL : (↑K : Set (Word α)) ⊆ L := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwC | hwC'
    · exact hC.1 hwC
    · exact hsub (hC'.1 hwC')

  have hKL' : (↑K : Set (Word α)) ⊆ L' := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwC | hwC'
    · exact hCsub hwC
    · exact hC'.1 hwC'

  have hEqL : B K = L :=
    hC.2 K hCK hKL
  have hEqL' : B K = L' :=
    hC'.2 K hC'K hKL'
  exact hne (hEqL.symm.trans hEqL')

end TCS1
end LeanCfgProject
