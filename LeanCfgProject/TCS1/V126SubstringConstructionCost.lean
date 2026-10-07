import LeanCfgProject.TCS1.V121SubstringCost
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# TCS #1 v126: exact context/type buckets and quartic output envelope

This file fills the missing representation-level bridge in the current
polynomial-reconstruction proof.  The manuscript's unary-rule enumeration
groups *observed occurrences* by the exact surrounding context (u,v) and the
fixed h-value of the factor.  We define those buckets on the finite two-cut
occurrence space and verify:

* every nonempty occurrence belongs to exactly one bucket;
* a fixed bucket contains at most one occurrence from each sample word;
* hence every bucket has size at most |K|;
* the total bucket population is at most n_K^2;
* therefore the total number of ordered pairs emitted by all unary buckets is
  at most n_K^3;
* together with the existing split-space and distinct-factor bounds, all rule
  candidates are cubic and a literal O(n_K)-per-production encoding is
  quartic.

This is the exact combinatorial content of the O(n_K^4) paragraph of the
v126 manuscript.  It is a finite enumeration/output-size theorem; a chosen
machine instruction cost model is kept separate.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V126SubstringConstructionCost

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]

/-- Finite key used by Rule (U): exact left/right context and fixed h-value. -/
structure V126OccurrenceKey
    (α : Type u) (M : Type v) where
  leftContext : Word α
  rightContext : Word α
  typ : M
deriving DecidableEq

/-- Nonempty two-cut occurrences.  Invalid/reversed cuts decode to the empty
factor and are discarded. -/
noncomputable def v126ValidOccurrences
    (K : Finset (Word α)) :
    Finset (ReconstructionFactorSlot K) := by
  classical
  exact
    (Finset.univ : Finset (ReconstructionFactorSlot K)).filter
      (fun s =>
        (reconstructionFactorSlotNonterminal s).factor ≠ [])

/-- The exact context/type key used by the manuscript's unary buckets. -/
def v126OccurrenceKey
    (H : FixedFiniteMonoidHom α M)
    {K : Finset (Word α)}
    (s : ReconstructionFactorSlot K) :
    V126OccurrenceKey α M :=
  { leftContext :=
      (reconstructionFactorSlotNonterminal s).leftContext
    rightContext :=
      (reconstructionFactorSlotNonterminal s).rightContext
    typ :=
      H.h (reconstructionFactorSlotNonterminal s).factor }

/-- Only keys that actually occur are enumerated. -/
noncomputable def v126OccurrenceKeys
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Finset (V126OccurrenceKey α M) := by
  classical
  exact (v126ValidOccurrences K).image (v126OccurrenceKey H)

/-- One exact context/type bucket. -/
noncomputable def v126OccurrenceBucket
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (key : V126OccurrenceKey α M) :
    Finset (ReconstructionFactorSlot K) := by
  classical
  exact
    (v126ValidOccurrences K).filter
      (fun s => v126OccurrenceKey H s = key)

/-- Two slots cut from the same sampled word and having the same left/right
contexts are identical.  The h-component of the key is not needed for this
injectivity fact. -/
theorem v126_slot_eq_of_same_word_and_key
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {s t : ReconstructionFactorSlot K}
    (hword : s.1.1 = t.1.1)
    (hkey : v126OccurrenceKey H s = v126OccurrenceKey H t) :
    s = t := by
  rcases s with ⟨⟨ws, hws⟩, ⟨is, js⟩⟩
  rcases t with ⟨⟨wt, hwt⟩, ⟨it, jt⟩⟩
  dsimp at hword
  subst wt
  have hleft :
      ws.take is.val = ws.take it.val := by
    have h :=
      congrArg
        (fun q : V126OccurrenceKey α M => q.leftContext)
        hkey
    simpa [v126OccurrenceKey,
      reconstructionFactorSlotNonterminal] using h
  have hright :
      ws.drop js.val = ws.drop jt.val := by
    have h :=
      congrArg
        (fun q : V126OccurrenceKey α M => q.rightContext)
        hkey
    simpa [v126OccurrenceKey,
      reconstructionFactorSlotNonterminal] using h
  have hislt := is.isLt
  have hitlt := it.isLt
  have hjslt := js.isLt
  have hjtlt := jt.isLt
  change is.val < ws.length + 1 at hislt
  change it.val < ws.length + 1 at hitlt
  change js.val < ws.length + 1 at hjslt
  change jt.val < ws.length + 1 at hjtlt
  have his : is.val ≤ ws.length := by omega
  have hit : it.val ≤ ws.length := by omega
  have hjs : js.val ≤ ws.length := by omega
  have hjt : jt.val ≤ ws.length := by omega
  have hi : is.val = it.val := by
    have hlen := congrArg List.length hleft
    simpa [List.length_take, Nat.min_eq_left his,
      Nat.min_eq_left hit] using hlen
  have hj : js.val = jt.val := by
    have hlen := congrArg List.length hright
    simp only [List.length_drop] at hlen
    omega
  have hisEq : is = it := Fin.ext hi
  have hjsEq : js = jt := Fin.ext hj
  have hp : hws = hwt := Subsingleton.elim _ _
  cases hp
  cases hisEq
  cases hjsEq
  rfl

/-- A context/type bucket has at most one entry from each sample word. -/
theorem v126_bucket_card_le_sample_card
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (key : V126OccurrenceKey α M) :
    (v126OccurrenceBucket H K key).card ≤ K.card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun s : ReconstructionFactorSlot K => s.1.1)
  · intro s hs
    exact s.1.2
  · intro s hs t ht hword
    have hskey :
        v126OccurrenceKey H s = key := by
      exact (Finset.mem_filter.mp hs).2
    have htkey :
        v126OccurrenceKey H t = key := by
      exact (Finset.mem_filter.mp ht).2
    exact
      v126_slot_eq_of_same_word_and_key
        H K hword (hskey.trans htkey.symm)

/-- Summing bucket cardinalities counts exactly the valid occurrences. -/
theorem v126_sum_bucket_cards_eq_valid
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    (∑ key ∈ v126OccurrenceKeys H K,
        (v126OccurrenceBucket H K key).card)
      =
    (v126ValidOccurrences K).card := by
  classical
  unfold v126OccurrenceKeys v126OccurrenceBucket
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

/-- Total unary-bucket population is quadratically bounded by sample norm. -/
theorem v126_sum_bucket_cards_le_sq
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    (∑ key ∈ v126OccurrenceKeys H K,
        (v126OccurrenceBucket H K key).card)
      ≤
    (reconstructionSampleNorm K) ^ 2 := by
  rw [v126_sum_bucket_cards_eq_valid H K]
  calc
    (v126ValidOccurrences K).card
        ≤ Fintype.card (ReconstructionFactorSlot K) := by
          simpa [v126ValidOccurrences] using
            (Finset.card_filter_le
              (Finset.univ : Finset (ReconstructionFactorSlot K))
              (fun s =>
                (reconstructionFactorSlotNonterminal s).factor ≠ []))
    _ ≤ (reconstructionSampleNorm K) ^ 2 :=
      reconstructionFactorSlot_card_le_sq K

/-- Exact ordered-pair count emitted by all unary buckets. -/
noncomputable def v126UnaryPairCount
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Nat :=
  ∑ key ∈ v126OccurrenceKeys H K,
    (v126OccurrenceBucket H K key).card ^ 2

/-- Rule (U) emits at most n_K^3 ordered pairs. -/
theorem v126UnaryPairCount_le_cube
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    v126UnaryPairCount H K ≤
      (reconstructionSampleNorm K) ^ 3 := by
  unfold v126UnaryPairCount
  calc
    (∑ key ∈ v126OccurrenceKeys H K,
        (v126OccurrenceBucket H K key).card ^ 2)
      ≤
    K.card *
      (∑ key ∈ v126OccurrenceKeys H K,
        (v126OccurrenceBucket H K key).card) := by
      calc
        (∑ key ∈ v126OccurrenceKeys H K,
            (v126OccurrenceBucket H K key).card ^ 2)
          ≤
        ∑ key ∈ v126OccurrenceKeys H K,
          K.card * (v126OccurrenceBucket H K key).card := by
            apply Finset.sum_le_sum
            intro key hkey
            have hcap :=
              v126_bucket_card_le_sample_card H K key
            nlinarith
        _ =
        K.card *
          (∑ key ∈ v126OccurrenceKeys H K,
            (v126OccurrenceBucket H K key).card) := by
              rw [Finset.mul_sum]
    _ ≤
      (reconstructionSampleNorm K) *
        (reconstructionSampleNorm K) ^ 2 := by
          exact Nat.mul_le_mul
            (reconstructionSample_card_le_norm K)
            (v126_sum_bucket_cards_le_sq H K)
    _ = (reconstructionSampleNorm K) ^ 3 := by ring

/-- Generous exact candidate count for the current substring constructor:
start rules, lexical factor states, binary split slots, and unary bucket pairs. -/
noncomputable def v126RuleCandidateCount
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Nat :=
  K.card +
    (v121FactorCandidates K).card +
    Fintype.card (ReconstructionSplitSlot K) +
    v126UnaryPairCount H K

/-- All current rule-candidate families together are cubic. -/
theorem v126RuleCandidateCount_le_cubic
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    v126RuleCandidateCount H K ≤
      4 * (reconstructionSampleNorm K + 1) ^ 3 := by
  have h1 := reconstructionSample_card_le_norm K
  have h2 := v121_factorCandidates_card_le_sq K
  have h3 := reconstructionSplitSlot_card_le_cube K
  have hu := v126UnaryPairCount_le_cube H K
  unfold v126RuleCandidateCount
  nlinarith [Nat.zero_le (reconstructionSampleNorm K)]

/-- A conservative literal output envelope.  Three factor identifiers per
production, each of length at most n_K, plus constant delimiters, suffice for
the manuscript's O(n_K)-per-production representation claim. -/
noncomputable def v126LiteralOutputEnvelope
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Nat :=
  v126RuleCandidateCount H K *
    (3 * reconstructionSampleNorm K + 1)

/-- The explicit stored grammar output is bounded by a degree-four polynomial,
matching the O(n_K^4) statement in the current manuscript. -/
theorem v126LiteralOutputEnvelope_le_quartic
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    v126LiteralOutputEnvelope H K ≤
      16 * (reconstructionSampleNorm K + 1) ^ 4 := by
  unfold v126LiteralOutputEnvelope
  have hc := v126RuleCandidateCount_le_cubic H K
  have hl :
      3 * reconstructionSampleNorm K + 1 ≤
        4 * (reconstructionSampleNorm K + 1) := by omega
  calc
    v126RuleCandidateCount H K *
          (3 * reconstructionSampleNorm K + 1)
      ≤
    (4 * (reconstructionSampleNorm K + 1) ^ 3) *
      (4 * (reconstructionSampleNorm K + 1)) :=
        Nat.mul_le_mul hc hl
    _ = 16 * (reconstructionSampleNorm K + 1) ^ 4 := by ring

end V126SubstringConstructionCost

end TCS1
end LeanCfgProject
