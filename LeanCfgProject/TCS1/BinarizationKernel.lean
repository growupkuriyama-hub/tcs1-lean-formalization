import LeanCfgProject.TCS1.TerminalIsolationKernel
import LeanCfgProject.TCS1.SSBNFThicknessBounds

/-!
# TCS #1 v65: binarization kernel

After terminal isolation, every right-hand side of length at least two can be
viewed as a list of nonterminals. Appendix A replaces a long list by a
right-associated chain of fresh suffix nonterminals. This module checks the
semantic and thickness cores of that construction.

A fresh suffix state for B_2 ... B_m denotes exactly the concatenation
language of that contiguous block. Therefore replacing
A -> B_1 ... B_m by A -> B_1 C_2 and recursively expanding C_2 preserves
the words realized by the original right-hand side. The same representation
also gives the quantitative fact that a suffix containing at most n symbols
has a terminal witness of length at most n times the common child-yield bound.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section Binarization

variable {N : Type u}
variable {α : Type v}

/-- Concatenation language realized by a sequence of nonterminals. -/
def NTSequenceRealizes
    (L : N → Set (List α)) :
    List N → List α → Prop
  | [], w =>
      w = []
  | A :: rest, w =>
      ∃ u v,
        w = u ++ v ∧
        u ∈ L A ∧
        NTSequenceRealizes L rest v

/--
One binary concatenation step under a supplied nonterminal interpretation.
-/
def BinaryPairRealizes
    {X : Type u}
    (L : X → Set (List α))
    (B C : X)
    (w : List α) : Prop :=
  ∃ u v,
    w = u ++ v ∧
    u ∈ L B ∧
    v ∈ L C

/-- Old symbols together with fresh states naming nonempty suffix blocks. -/
inductive BinarizedState (N : Type u)
  | old : N → BinarizedState N
  | suffix : List N → BinarizedState N
deriving DecidableEq

/-- Semantic interpretation of old and fresh suffix states. -/
def binarizedInterpretation
    (L : N → Set (List α)) :
    BinarizedState N → Set (List α)
  | BinarizedState.old A => L A
  | BinarizedState.suffix xs =>
      {w | NTSequenceRealizes L xs w}

/--
A two-symbol nonterminal sequence is exactly one binary concatenation step.
-/
theorem ntSequence_two_iff_binaryPair
    {X : Type u}
    (L : X → Set (List α))
    (B C : X)
    (w : List α) :
    NTSequenceRealizes L [B, C] w ↔
      BinaryPairRealizes L B C w := by
  constructor
  · intro h
    rcases h with ⟨u, v, hw, hu, hv⟩
    rcases hv with ⟨vC, tail, hvEq, hvC, htail⟩
    have htailNil : tail = [] := htail
    subst tail
    have hvEq' : v = vC := by
      simpa using hvEq
    subst v
    have hw' : w = u ++ vC := by
      simpa using hw
    exact ⟨u, vC, hw', hu, hvC⟩
  · intro h
    rcases h with ⟨u, v, hw, hu, hv⟩
    refine ⟨u, v, hw, hu, ?_⟩
    exact ⟨v, [], by simp, hv, rfl⟩

/-- Sequence realization is monotone in the interpretation of nonterminals. -/
theorem ntSequenceRealizes_mono
    {X : Type u}
    {L₁ L₂ : X → Set (List α)}
    (hsub : ∀ A, L₁ A ⊆ L₂ A)
    {xs : List X}
    {w : List α}
    (h : NTSequenceRealizes L₁ xs w) :
    NTSequenceRealizes L₂ xs w := by
  induction xs generalizing w with
  | nil =>
      exact h
  | cons A rest ih =>
      rcases h with ⟨u, v, hw, hu, hv⟩
      exact ⟨u, v, hw, hsub A hu, ih hv⟩

/--
Binary concatenation on two embedded old states is definitionally the source
binary concatenation, made explicit for downstream rewriting.
-/
theorem binaryPair_old_iff
    (L : N → Set (List α))
    (B C : N)
    (w : List α) :
    BinaryPairRealizes
        (binarizedInterpretation L)
        (BinarizedState.old B)
        (BinarizedState.old C)
        w
      ↔
    BinaryPairRealizes L B C w := by
  simp [BinaryPairRealizes, binarizedInterpretation]

/--
A sequence of embedded old states realizes exactly the same terminal words as
the corresponding source-state sequence.
-/
theorem ntSequence_old_map_iff
    (L : N → Set (List α))
    (xs : List N)
    (w : List α) :
    NTSequenceRealizes
        (binarizedInterpretation L)
        (xs.map BinarizedState.old)
        w
      ↔
    NTSequenceRealizes L xs w := by
  induction xs generalizing w with
  | nil =>
      simp [NTSequenceRealizes]
  | cons A rest ih =>
      simp [NTSequenceRealizes, binarizedInterpretation, ih]

/--
The first binary split of a long RHS is semantically exact.
-/
theorem first_binary_split_iff
    (L : N → Set (List α))
    (A B : N)
    (rest : List N)
    (w : List α) :
    NTSequenceRealizes L (A :: B :: rest) w ↔
      BinaryPairRealizes
        (binarizedInterpretation L)
        (BinarizedState.old A)
        (BinarizedState.suffix (B :: rest))
        w := by
  constructor
  · intro h
    rcases h with ⟨u, v, hw, hu, hv⟩
    exact ⟨u, v, hw, hu, hv⟩
  · intro h
    rcases h with ⟨u, v, hw, hu, hv⟩
    exact ⟨u, v, hw, hu, hv⟩

/--
Every fresh suffix state is decomposed by the same binary equation.
-/
theorem suffix_binary_split_iff
    (L : N → Set (List α))
    (A B : N)
    (rest : List N)
    (w : List α) :
    w ∈ binarizedInterpretation L
          (BinarizedState.suffix (A :: B :: rest))
      ↔
    BinaryPairRealizes
      (binarizedInterpretation L)
      (BinarizedState.old A)
      (BinarizedState.suffix (B :: rest))
      w := by
  exact first_binary_split_iff L A B rest w

/--
The final length-two suffix is realized by one ordinary binary pair.
-/
theorem final_binary_pair_iff
    (L : N → Set (List α))
    (A B : N)
    (w : List α) :
    NTSequenceRealizes L [A, B] w ↔
      BinaryPairRealizes
        (binarizedInterpretation L)
        (BinarizedState.old A)
        (BinarizedState.old B)
        w := by
  constructor
  · intro h
    rcases h with ⟨u, v, hw, hu, hv⟩
    have hv' : v ∈ L B := by
      rcases hv with ⟨vB, tail, hvEq, hvB, htail⟩
      have htailNil : tail = [] := htail
      subst tail
      have hvEq' : v = vB := by
        simpa using hvEq
      rw [hvEq']
      exact hvB
    exact ⟨u, v, hw, hu, hv'⟩
  · intro h
    rcases h with ⟨u, v, hw, hu, hv⟩
    refine ⟨u, v, hw, hu, ?_⟩
    exact ⟨v, [], by simp, hv, rfl⟩

/--
If every child nonterminal has some terminal yield of length at most tau,
then every sequence has a concatenated witness of length at most
(sequence length) * tau.
-/
theorem sequence_short_witness
    (L : N → Set (List α))
    (τ : Nat)
    (hshort : ∀ A, ∃ w, w ∈ L A ∧ w.length ≤ τ)
    (xs : List N) :
    ∃ w,
      NTSequenceRealizes L xs w ∧
      w.length ≤ xs.length * τ := by
  induction xs with
  | nil =>
      exact ⟨[], rfl, by simp⟩
  | cons A rest ih =>
      obtain ⟨u, hu, hlenU⟩ := hshort A
      obtain ⟨v, hv, hlenV⟩ := ih
      refine ⟨u ++ v, ?_, ?_⟩
      · exact ⟨u, v, rfl, hu, hv⟩
      · simp only [List.length_append, List.length_cons]
        calc
          u.length + v.length
            ≤ τ + rest.length * τ :=
              Nat.add_le_add hlenU hlenV
          _ = (rest.length + 1) * τ := by ring

/--
A fresh suffix spanning at most n old symbols has a witness bounded by
n * tau.
-/
theorem suffix_short_witness_of_length_le
    (L : N → Set (List α))
    (τ n : Nat)
    (hshort : ∀ A, ∃ w, w ∈ L A ∧ w.length ≤ τ)
    (xs : List N)
    (hlen : xs.length ≤ n) :
    ∃ w,
      w ∈ binarizedInterpretation L (BinarizedState.suffix xs) ∧
      w.length ≤ n * τ := by
  obtain ⟨w, hw, hbound⟩ :=
    sequence_short_witness L τ hshort xs
  refine ⟨w, hw, ?_⟩
  exact le_trans hbound (Nat.mul_le_mul_right τ hlen)

/--
Appendix-facing specialization with the harmless positive envelope tau_R+1.
-/
theorem suffix_short_witness_thicknessBar
    (L : N → Set (List α))
    (n τR : Nat)
    (hshort :
      ∀ A, ∃ w, w ∈ L A ∧ w.length ≤ thicknessBar τR)
    (xs : List N)
    (hlen : xs.length ≤ n) :
    ∃ w,
      w ∈ binarizedInterpretation L (BinarizedState.suffix xs) ∧
      w.length ≤ n * thicknessBar τR :=
  suffix_short_witness_of_length_le
    L (thicknessBar τR) n hshort xs hlen

end Binarization

end TCS1
end LeanCfgProject
