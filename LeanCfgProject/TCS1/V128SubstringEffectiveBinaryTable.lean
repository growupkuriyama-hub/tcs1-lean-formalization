import LeanCfgProject.TCS1.V128SubstringBinarySplitSlots

/-!
# TCS #1 v128: executable word-coded binary-production enumeration

The CI #877 proof injects all actual (B) rules into the existing cubic
three-cut index space. Here the finite candidate image and its validity
filter are defined using ordinary computable Finset operations, rather than
the classical filtered univ of proof-carrying observed-factor triples.

A two-cut scan discovers exactly the nonempty factors appearing in K.
A three-cut scan creates candidates (parent,left,right); the filter retains
exactly those whose parent occurs, decomposes as left ++ right, and has
two nonempty children. The final output is a Finset of *word codes*;
duplicate rules are removed by Finset.image/filter semantics.

This alone does NOT bound execution steps for comparing/deduplicating large
word keys, nor serialize stable integer state identifiers. In particular
the Big-O(n_K^4) runtime theorem remains separately open.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section EffectiveBinaryWordEnumeration

variable {α : Type u} {M : Type v}
variable [Fintype α] [DecidableEq α] [Monoid M] [Fintype M]

/-- Finite two-cut scan of words that actually occur as nonempty factors.
    Both the decoded factor and its surrounding contexts are checked
    against the original sample; invalid cut pairs cannot add words. -/
def v116EffectiveObservedFactorWords
    (K : Finset (Word α)) : Finset (Word α) :=
  ((Finset.univ : Finset (ReconstructionFactorSlot K)).filter
    (fun s =>
      let t := reconstructionFactorSlotNonterminal s
      t.factor ≠ [] ∧ t.leftContext ++ t.factor ++ t.rightContext ∈ K)
  ).image (fun s => (reconstructionFactorSlotNonterminal s).factor)

/-- The two-cut scan has precisely the semantic observed nonempty factors. -/
theorem v116EffectiveObservedFactorWords_iff
    (K : Finset (Word α)) (x : Word α) :
    x ∈ v116EffectiveObservedFactorWords K ↔
      ∃ p q : Word α, Observed K x p q := by
  classical
  constructor
  · intro hx
    obtain ⟨s, hs, hsx⟩ := Finset.mem_image.mp hx
    have hvalid := (Finset.mem_filter.mp hs).2
    change (reconstructionFactorSlotNonterminal s).factor ≠ [] ∧
      (reconstructionFactorSlotNonterminal s).leftContext ++
        (reconstructionFactorSlotNonterminal s).factor ++
        (reconstructionFactorSlotNonterminal s).rightContext ∈ K at hvalid
    rw [← hsx]
    exact ⟨(reconstructionFactorSlotNonterminal s).leftContext,
      (reconstructionFactorSlotNonterminal s).rightContext, hvalid⟩
  · rintro ⟨p, q, hobs⟩
    apply Finset.mem_image.mpr
    refine ⟨observedReconstructionFactorSlot K hobs, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [reconstructionFactorSlotNonterminal_observed] using hobs
    · simpa [reconstructionFactorSlotNonterminal_observed]

/-- The raw three-cut decoder, now given by a transparent computable def.
    It agrees definitionally with the earlier noncomputable mathematical
    candidate set from CI #877. -/
def v116EffectiveRawBinaryCodes
    (K : Finset (Word α)) :
    Finset (Word α × (Word α × Word α)) :=
  (Finset.univ : Finset (ReconstructionSplitSlot K)).image
    (v116BinarySplitCode (K := K))

theorem v116EffectiveRawBinaryCodes_eq
    (K : Finset (Word α)) :
    v116EffectiveRawBinaryCodes K = v116BinarySplitCodes K := by
  rfl

/-- Filter raw three-cut codes by decidable factor occurrence and the
    exact nonempty split conditions. This is the *computable* binary table
    on word identifiers; invalid cuts are rejected. -/
def v116EffectiveBinaryWordTable
    (K : Finset (Word α)) :
    Finset (Word α × (Word α × Word α)) :=
  (v116EffectiveRawBinaryCodes K).filter
    (fun e => e.1 = e.2.1 ++ e.2.2 ∧
      e.2.1 ≠ [] ∧ e.2.2 ≠ [] ∧
      e.1 ∈ v116EffectiveObservedFactorWords K)

/-- Exact, source-independent meaning of the executable membership test. -/
theorem v116EffectiveBinaryWordTable_iff
    (K : Finset (Word α)) (x y z : Word α) :
    (x, (y, z)) ∈ v116EffectiveBinaryWordTable K ↔
      x = y ++ z ∧ y ≠ [] ∧ z ≠ [] ∧
        ∃ p q : Word α, Observed K x p q := by
  classical
  constructor
  · intro he
    have hv := (Finset.mem_filter.mp he).2
    exact ⟨hv.1, hv.2.1, hv.2.2.1,
      (v116EffectiveObservedFactorWords_iff K x).mp hv.2.2.2⟩
  · rintro ⟨hxyz, hy, hz, p, q, hobs⟩
    have hleft : Observed K y p (z ++ q) := by
      constructor
      · exact hy
      · simpa only [List.append_assoc, ← hxyz] using hobs.2
    have hright : Observed K z (p ++ y) q := by
      constructor
      · exact hz
      · simpa only [List.append_assoc, ← hxyz] using hobs.2
    have hraw :
        (x, (y, z)) ∈ v116EffectiveRawBinaryCodes K := by
      have hc := v116BinarySplitCodes_cover K
        (⟨x, ⟨p, q, hobs⟩⟩ : ObservedSubstringNonterminal K)
        (⟨y, ⟨p, z ++ q, hleft⟩⟩ : ObservedSubstringNonterminal K)
        (⟨z, ⟨p ++ y, q, hright⟩⟩ : ObservedSubstringNonterminal K)
        hxyz
      rw [v116EffectiveRawBinaryCodes_eq]
      exact hc
    apply Finset.mem_filter.mpr
    exact ⟨hraw, hxyz, hy, hz,
      (v116EffectiveObservedFactorWords_iff K x).mpr
        ⟨p, q, hobs⟩⟩

/-- The executable binary word-code set is the image of exactly the
    previously Lean-verified finite v116 (B) production table. -/
theorem v116EffectiveBinaryWordTable_eq_actual
    (K : Finset (Word α)) :
    v116EffectiveBinaryWordTable K =
      (v116BinaryRuleTable K).image
        (v116BinaryProductionWordCode (K := K)) := by
  classical
  ext e
  rcases e with ⟨x, ⟨y, z⟩⟩
  constructor
  · intro he
    rcases (v116EffectiveBinaryWordTable_iff K x y z).mp he with
      ⟨hxyz, hy, hz, p, q, hobs⟩
    have hleft : Observed K y p (z ++ q) := by
      constructor
      · exact hy
      · simpa only [List.append_assoc, ← hxyz] using hobs.2
    have hright : Observed K z (p ++ y) q := by
      constructor
      · exact hz
      · simpa only [List.append_assoc, ← hxyz] using hobs.2
    let A : ObservedSubstringNonterminal K := ⟨x, ⟨p, q, hobs⟩⟩
    let B : ObservedSubstringNonterminal K := ⟨y, ⟨p, z ++ q, hleft⟩⟩
    let C : ObservedSubstringNonterminal K := ⟨z, ⟨p ++ y, q, hright⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨(A, (B, C)), ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxyz⟩
  · intro he
    obtain ⟨e, he, hcode⟩ := Finset.mem_image.mp he
    rcases e with ⟨A, B, C⟩
    have hxyz : A.1 = B.1 ++ C.1 := by
      exact (Finset.mem_filter.mp he).2
    have hactual :
        (A.1, (B.1, C.1)) ∈
          v116EffectiveBinaryWordTable K := by
      exact (v116EffectiveBinaryWordTable_iff K A.1 B.1 C.1).mpr
        ⟨hxyz, observedSubstring_ne_nil K B,
          observedSubstring_ne_nil K C, A.2⟩
    change (A.1, (B.1, C.1)) = (x, (y, z)) at hcode
    rw [← hcode]
    exact hactual

/-- The number of distinct executable word-coded rules is ≤ n_K³.
    This is an output-cardinality bound; it is not a step-count bound
    for Finset.image/filter comparisons. -/
theorem v116EffectiveBinaryWordTable_card_le_cube
    (K : Finset (Word α)) :
    (v116EffectiveBinaryWordTable K).card ≤
      (reconstructionSampleNorm K) ^ 3 := by
  calc
    (v116EffectiveBinaryWordTable K).card ≤
        (v116EffectiveRawBinaryCodes K).card :=
      Finset.card_filter_le _ _
    _ = (v116BinarySplitCodes K).card := by
      rw [v116EffectiveRawBinaryCodes_eq]
    _ ≤ (reconstructionSampleNorm K) ^ 3 :=
      v116BinarySplitCodes_card_le_cube K

end EffectiveBinaryWordEnumeration

end TCS1
end LeanCfgProject
