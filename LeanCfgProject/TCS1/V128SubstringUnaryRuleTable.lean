import LeanCfgProject.TCS1.V128SubstringQuarticEnvelope

/-!
# TCS #1 v128: a literal finite (U) production table for the v116 grammar

The earlier cubic theorem counted all pairs from finitely enumerated
context/type buckets. This module takes the next step: it decodes those
pairs into a *finite set of actual word-indexed unary productions*, and
proves that membership is **equivalent** to the v116 rule predicate
`SubstringUnaryRelated`.

It does not change the old v88 grammar or learner.
This is still a noncomputable finite-set presentation: a separate
effective implementation, canonical state IDs, printing cost and
whole-emitter step bound remain necessary for an O(||K||^4)
machine-time claim.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section LiteralV116UnaryTable

variable {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M] [Fintype M]

/-- Finite candidate indices: one occupied context/type key and an ordered
    pair of factors in its bucket. -/
abbrev V116UnaryCandidate
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :=
  Σ b : {b : ((Word α × Word α) × M) //
      b ∈ substringBucketKeys H K},
    SubstringContextBucket H K b.1.1.1 b.1.1.2 b.1.2 ×
    SubstringContextBucket H K b.1.1.1 b.1.1.2 b.1.2

noncomputable instance v116UnaryCandidateFintype
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Fintype (V116UnaryCandidate H K) := by
  classical
  infer_instance

/-- Decode one candidate into its literal (U) rule, with the factor
    words as identifiers for the distinct observed substring states. -/
def v116UnaryCandidateRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (e : V116UnaryCandidate H K) :
    Word α × Word α :=
  (e.2.1.1.1, e.2.2.1.1)

/-- The finite image of the enumerated candidates. Duplicate (U) rules
    are removed by finset-image semantics. -/
noncomputable def v116UnaryRuleTable
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Finset (Word α × Word α) := by
  classical
  exact Finset.univ.image (v116UnaryCandidateRule H K)

/-- Every produced rule is a genuine v116 (U) rule. -/
theorem v116UnaryRuleTable_sound
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x y : Word α}
    (h : (x, y) ∈ v116UnaryRuleTable H K) :
    SubstringUnaryRelated H K x y := by
  classical
  unfold v116UnaryRuleTable at h
  obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
  have hx : e.2.1.1.1 = x := congrArg Prod.fst he
  have hy : e.2.2.1.1 = y := congrArg Prod.snd he
  rw [← hx, ← hy]
  exact ⟨(e.2.1.2.2).trans (e.2.2.2.2).symm,
    e.1.1.1.1, e.1.1.1.2, e.2.1.2.1, e.2.2.2.1⟩

/-- Every semantic v116 (U) rule occurs in the finite table. -/
theorem v116UnaryRuleTable_complete
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x y : Word α}
    (h : SubstringUnaryRelated H K x y) :
    (x, y) ∈ v116UnaryRuleTable H K := by
  classical
  obtain ⟨p, q, μ, hk, A, B, hx, hy⟩ :=
    substringBucketKeys_covers_unary H K h
  unfold v116UnaryRuleTable
  apply Finset.mem_image.mpr
  refine ⟨(⟨⟨((p, q), μ), hk⟩, (A, B)⟩ :
      V116UnaryCandidate H K), Finset.mem_univ _, ?_⟩
  exact Prod.ext hx hy

/-- The literal table matches the finite CFG's unit-rule predicate exactly. -/
theorem v116UnaryRuleTable_iff
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A B : ObservedSubstringNonterminal K) :
    (A.1, B.1) ∈ v116UnaryRuleTable H K ↔
      (finiteSubstringGrammar H K).unitRule A B := by
  change (A.1, B.1) ∈ v116UnaryRuleTable H K ↔
    SubstringUnaryRelated H K A.1 B.1
  exact ⟨v116UnaryRuleTable_sound H K,
    v116UnaryRuleTable_complete H K⟩

/-- The candidate type has exactly the previously counted bucket-pair size. -/
theorem v116UnaryCandidate_card_eq
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Fintype.card (V116UnaryCandidate H K) =
      ∑ b ∈ substringBucketKeys H K,
        (Fintype.card
          (SubstringContextBucket H K b.1.1 b.1.2 b.2)) ^ 2 := by
  classical
  simp only [V116UnaryCandidate, Fintype.card_sigma, Fintype.card_prod]
  rw [← Finset.attach_eq_univ]
  simp only [pow_two]
  exact Finset.sum_attach (substringBucketKeys H K)
    (fun b =>
      Fintype.card (SubstringContextBucket H K b.1.1 b.1.2 b.2) *
      Fintype.card (SubstringContextBucket H K b.1.1 b.1.2 b.2))

/-- **Unconditional cubic bound on the actual finite (U) rule table.**
    No external rule-count assumption is used. -/
theorem v116UnaryRuleTable_card_le_cube
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    (v116UnaryRuleTable H K).card ≤
      (reconstructionSampleNorm K) ^ 3 := by
  classical
  calc
    (v116UnaryRuleTable H K).card ≤
        Fintype.card (V116UnaryCandidate H K) := by
      unfold v116UnaryRuleTable
      simpa using (Finset.card_image_le
        (s := (Finset.univ : Finset (V116UnaryCandidate H K)))
        (f := v116UnaryCandidateRule H K))
    _ = ∑ b ∈ substringBucketKeys H K,
        (Fintype.card
          (SubstringContextBucket H K b.1.1 b.1.2 b.2)) ^ 2 :=
      v116UnaryCandidate_card_eq H K
    _ ≤ (reconstructionSampleNorm K) ^ 3 :=
      substringBucketKeys_unaryCandidateCount_le_cube H K

end LiteralV116UnaryTable

end TCS1
end LeanCfgProject
