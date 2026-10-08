import LeanCfgProject.TCS1.V128SubstringBucketCount

/-!
# TCS #1 v128: unconditional quadratic count of all U-bucket entries

For *any* finite collection B of context/type keys, an entry in a
v116 unary-rule bucket is exactly a nonempty factor x at a context
(p,q) and type h(x). Sending that entry to the sample word
p ++ x ++ q and the two cut positions |p|, |p|+|x| is injective.
The reconstructed occurrence triple recovers p, x, q; the type μ
is h(x). Hence all bucket entries together inject into the old,
already verified, two-cut occurrence-slot finite type.

This derives the O(n_K^2) entry bound without an assumed hentries
hypothesis, and therefore the O(n_K^3) total unary-pair bound.

A final bridge to a concrete computable set B of ALL occupied keys,
and the literal rule encoding/time cost, is separate.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section QuadraticBucketEntries

variable {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M] [Fintype M]

/-- Entries in a finite set of context/type keys. -/
abbrev SubstringBucketEntries
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (B : Finset ((Word α × Word α) × M)) :=
  Σ b : {b : ((Word α × Word α) × M) // b ∈ B},
    SubstringContextBucket H K b.1.1.1 b.1.1.2 b.1.2

noncomputable instance substringBucketEntriesFintype
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (B : Finset ((Word α × Word α) × M)) :
    Fintype (SubstringBucketEntries H K B) := by
  classical
  infer_instance

/-- Send a bucket entry to its actual occurrence in a positive sample. -/
def substringBucketEntryToSlot
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (B : Finset ((Word α × Word α) × M))
    (e : SubstringBucketEntries H K B) :
    ReconstructionFactorSlot K :=
  observedReconstructionFactorSlot K e.2.2.1

/-- Different bucket entries cannot share the same two-cut sample slot. -/
theorem substringBucketEntryToSlot_injective
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (B : Finset ((Word α × Word α) × M)) :
    Function.Injective (substringBucketEntryToSlot H K B) := by
  intro e f h
  rcases e with ⟨be, ae⟩
  rcases f with ⟨bf, af⟩
  change observedReconstructionFactorSlot K ae.2.1 =
    observedReconstructionFactorSlot K af.2.1 at h
  have heq :
      (⟨ae.1.1, be.1.1.1, be.1.1.2⟩ : ReconstructionNonterminal α) =
        ⟨af.1.1, bf.1.1.1, bf.1.1.2⟩ := by
    calc
      (⟨ae.1.1, be.1.1.1, be.1.1.2⟩ : ReconstructionNonterminal α) =
          reconstructionFactorSlotNonterminal
            (observedReconstructionFactorSlot K ae.2.1) :=
        (reconstructionFactorSlotNonterminal_observed K ae.2.1).symm
      _ = reconstructionFactorSlotNonterminal
          (observedReconstructionFactorSlot K af.2.1) := by rw [h]
      _ = ⟨af.1.1, bf.1.1.1, bf.1.1.2⟩ :=
        reconstructionFactorSlotNonterminal_observed K af.2.1
  have hx : ae.1.1 = af.1.1 :=
    congrArg ReconstructionNonterminal.factor heq
  have hp : be.1.1.1 = bf.1.1.1 :=
    congrArg ReconstructionNonterminal.leftContext heq
  have hq : be.1.1.2 = bf.1.1.2 :=
    congrArg ReconstructionNonterminal.rightContext heq
  have hμ : be.1.2 = bf.1.2 := by
    calc
      be.1.2 = H.h ae.1.1 := ae.2.2.symm
      _ = H.h af.1.1 := congrArg H.h hx
      _ = bf.1.2 := af.2.2
  have hb : be = bf := by
    apply Subtype.ext
    apply Prod.ext
    · exact Prod.ext hp hq
    · exact hμ
  cases hb
  have ha : ae = af := by
    apply Subtype.ext
    apply Subtype.ext
    exact hx
  cases ha
  rfl

/-- All unary context/type bucket entries, for any finite key set,
    are bounded by the existing quadratic two-cut occurrence count. -/
theorem substringBucket_entries_le_factorSlots
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (B : Finset ((Word α × Word α) × M)) :
    (∑ b ∈ B,
      Fintype.card
        (SubstringContextBucket H K b.1.1 b.1.2 b.2)) ≤
      reconstructionFactorSlotCount K := by
  classical
  have hcard :
      Fintype.card (SubstringBucketEntries H K B) ≤
        Fintype.card (ReconstructionFactorSlot K) :=
    Fintype.card_le_of_injective
      (substringBucketEntryToSlot H K B)
      (substringBucketEntryToSlot_injective H K B)
  rw [reconstructionFactorSlot_card_eq] at hcard
  have hsum :
      Fintype.card (SubstringBucketEntries H K B) =
        ∑ b ∈ B, Fintype.card
          (SubstringContextBucket H K b.1.1 b.1.2 b.2) := by
    simp [SubstringBucketEntries, Fintype.card_sigma,
      ← Finset.attach_eq_univ] <;>
      exact Finset.sum_attach B
        (fun b => Fintype.card
          (SubstringContextBucket H K b.1.1 b.1.2 b.2))
  rwa [hsum] at hcard

/-- The actual O(n_K^3) pair-count consequence, with NO extra
    bucket-entry counting hypothesis. -/
theorem substringBucket_pairs_le_cube_unconditional
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (B : Finset ((Word α × Word α) × M)) :
    (∑ b ∈ B,
      (Fintype.card
        (SubstringContextBucket H K b.1.1 b.1.2 b.2)) ^ 2) ≤
      (reconstructionSampleNorm K) ^ 3 := by
  exact substringContextBucket_pairCount_le_cube H K B
    (substringBucket_entries_le_factorSlots H K B)

end QuadraticBucketEntries

end TCS1
end LeanCfgProject
