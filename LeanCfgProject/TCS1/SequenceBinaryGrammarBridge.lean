import LeanCfgProject.TCS1.BinarizationLeastClosed
import LeanCfgProject.TCS1.BinaryEpsilonElimination

/-!
# TCS #1 v66: bridge from binary sequence grammars to BinaryNullableGrammar

The normalization front end is represented by SequenceGrammar, while the
epsilon- and unit-elimination kernels use BinaryNullableGrammar. This file
connects the two semantics.

A sequence grammar is in binary form when every structural right-hand side is
empty, unary, or binary. Such a grammar has an evident binary grammar
presentation. We prove that its explicit derivation semantics is exactly the
least-closed sequence semantics. We also prove that the grammar produced by
binarizedSequenceGrammar is in binary form.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section SequenceBinaryGrammarBridge

variable {N : Type u}
variable {α : Type v}

/-- Every structural right-hand side is epsilon, unit, or binary. -/
def SequenceBinaryForm
    (G : SequenceGrammar N α) : Prop :=
  ∀ A rhs, G.structural A rhs →
    rhs = [] ∨
      (∃ B, rhs = [B]) ∨
      (∃ B C, rhs = [B, C])

/-- The evident binary/epsilon/unit presentation of a binary-form sequence grammar. -/
def sequenceToBinaryNullableGrammar
    (G : SequenceGrammar N α) :
    BinaryNullableGrammar N α where
  terminalRule := G.terminal
  binaryRule A B C := G.structural A [B, C]
  epsilonRule A := G.structural A []
  unitRule A B := G.structural A [B]

/-- The least-generated sequence language is itself closed under the grammar. -/
theorem sequenceLeastLanguage_closed
    (G : SequenceGrammar N α) :
    SequenceGrammarClosed G (SequenceLeastLanguage G) := by
  intro A w hw
  rcases hw with hterm | hstruct
  · rcases hterm with ⟨a, hGa, rfl⟩
    intro L hL
    exact hL A (Or.inl ⟨a, hGa, rfl⟩)
  · rcases hstruct with ⟨rhs, hG, hreal⟩
    intro L hL
    apply hL A
    right
    refine ⟨rhs, hG, ?_⟩
    have hsub :
        ∀ B,
          SequenceLeastLanguage G B ⊆ L B := by
      intro B u hu
      exact hu L hL
    exact ntSequenceRealizes_mono hsub hreal

/--
Any explicit binary derivation belongs to every closed interpretation of the
underlying sequence grammar.
-/
theorem binaryNullableDerives_mem_of_sequenceClosed
    (G : SequenceGrammar N α)
    (L : N → Set (List α))
    (hclosed : SequenceGrammarClosed G L)
    {A : N} {w : List α}
    (d : BinaryNullableDerives
      (sequenceToBinaryNullableGrammar G) A w) :
    w ∈ L A := by
  induction d with
  | @terminal A a h =>
      change G.terminal A a at h
      exact hclosed A (Or.inl ⟨a, h, rfl⟩)
  | @epsilon A h =>
      change G.structural A [] at h
      apply hclosed A
      right
      exact ⟨[], h, rfl⟩
  | @unit A B w h d ih =>
      change G.structural A [B] at h
      apply hclosed A
      right
      refine ⟨[B], h, ?_⟩
      exact ⟨w, [], by simp, ih, rfl⟩
  | @binary A B C wB wC h dB dC ihB ihC =>
      change G.structural A [B, C] at h
      apply hclosed A
      right
      refine ⟨[B, C], h, ?_⟩
      exact
        (ntSequence_two_iff_binaryPair L B C (wB ++ wC)).2
          ⟨wB, wC, rfl, ihB, ihC⟩

/--
For a binary-form sequence grammar, the family of explicitly derivable words
is closed under every sequence rule.
-/
theorem binaryDerivationLanguage_sequenceClosed
    (G : SequenceGrammar N α)
    (hform : SequenceBinaryForm G) :
    SequenceGrammarClosed G
      (fun A =>
        {w | BinaryNullableDerives
          (sequenceToBinaryNullableGrammar G) A w}) := by
  intro A w hw
  rcases hw with hterm | hstruct
  · rcases hterm with ⟨a, hGa, rfl⟩
    exact BinaryNullableDerives.terminal hGa
  · rcases hstruct with ⟨rhs, hG, hreal⟩
    rcases hform A rhs hG with hnil | hrest
    · subst rhs
      have hwNil : w = [] := hreal
      subst w
      exact BinaryNullableDerives.epsilon hG
    · rcases hrest with hunit | hbinary
      · rcases hunit with ⟨B, rfl⟩
        rcases hreal with ⟨u, v, hw, hu, hv⟩
        have hvNil : v = [] := hv
        have hwU : w = u := by
          simpa [hvNil] using hw
        rw [hwU]
        exact BinaryNullableDerives.unit hG hu
      · rcases hbinary with ⟨B, C, rfl⟩
        have hp :
            BinaryPairRealizes
              (fun X =>
                {u | BinaryNullableDerives
                  (sequenceToBinaryNullableGrammar G) X u})
              B C w :=
          (ntSequence_two_iff_binaryPair
            (fun X =>
              {u | BinaryNullableDerives
                (sequenceToBinaryNullableGrammar G) X u})
            B C w).1 hreal
        rcases hp with ⟨u, v, hw, hu, hv⟩
        rw [hw]
        exact BinaryNullableDerives.binary hG hu hv

/--
For binary-form sequence grammars, explicit derivability is equivalent to
membership in the least-generated sequence language.
-/
theorem binaryNullableDerives_iff_sequenceLeast
    (G : SequenceGrammar N α)
    (hform : SequenceBinaryForm G)
    (A : N)
    (w : List α) :
    BinaryNullableDerives
        (sequenceToBinaryNullableGrammar G) A w
      ↔
    w ∈ SequenceLeastLanguage G A := by
  constructor
  · intro d L hL
    exact binaryNullableDerives_mem_of_sequenceClosed
      G L hL d
  · intro hleast
    exact hleast
      (fun X =>
        {u | BinaryNullableDerives
          (sequenceToBinaryNullableGrammar G) X u})
      (binaryDerivationLanguage_sequenceClosed G hform)

/-- The output of the binarization construction is genuinely binary-form. -/
theorem binarizedSequenceGrammar_binaryForm
    (G : SequenceGrammar N α) :
    SequenceBinaryForm (binarizedSequenceGrammar G) := by
  intro X rhs h
  change BinarizedStructuralRule G X rhs at h
  cases h with
  | @source A sourceRhs hG =>
      cases sourceRhs with
      | nil =>
          exact Or.inl rfl
      | cons B rest =>
          cases rest with
          | nil =>
              exact Or.inr (Or.inl
                ⟨BinarizedState.old B, rfl⟩)
          | cons C rest₂ =>
              cases rest₂ with
              | nil =>
                  exact Or.inr (Or.inr
                    ⟨BinarizedState.old B,
                      BinarizedState.old C, rfl⟩)
              | cons D tail =>
                  exact Or.inr (Or.inr
                    ⟨BinarizedState.old B,
                      BinarizedState.suffix (C :: D :: tail), rfl⟩)
  | suffixEmpty =>
      exact Or.inl rfl
  | suffixUnit B =>
      exact Or.inr (Or.inl
        ⟨BinarizedState.old B, rfl⟩)
  | suffixBinary B C =>
      exact Or.inr (Or.inr
        ⟨BinarizedState.old B,
          BinarizedState.old C, rfl⟩)
  | suffixLong B C D rest =>
      exact Or.inr (Or.inr
        ⟨BinarizedState.old B,
          BinarizedState.suffix (C :: D :: rest), rfl⟩)

/-- Canonical binarized interpretations are monotone in source languages. -/
theorem binarizedInterpretation_mono
    {L₁ L₂ : N → Set (List α)}
    (hsub : ∀ A, L₁ A ⊆ L₂ A)
    (X : BinarizedState N) :
    binarizedInterpretation L₁ X ⊆
      binarizedInterpretation L₂ X := by
  cases X with
  | old A =>
      exact hsub A
  | suffix xs =>
      intro w hw
      exact ntSequenceRealizes_mono hsub hw

/--
The least language of every binary state, including fresh suffix states, is
its canonical suffix interpretation over the source least languages.
-/
theorem binarization_leastLanguage_all_eq
    (G : SequenceGrammar N α)
    (X : BinarizedState N) :
    SequenceLeastLanguage
        (binarizedSequenceGrammar G) X
      =
    binarizedInterpretation
      (SequenceLeastLanguage G) X := by
  apply Set.ext
  intro w
  constructor
  · intro hleast
    exact hleast
      (binarizedInterpretation
        (SequenceLeastLanguage G))
      (binarizedInterpretation_sequenceClosed
        G (SequenceLeastLanguage G)
        (sequenceLeastLanguage_closed G))
  · intro hcanonical Q hQ
    have hRestr :
        SequenceGrammarClosed G (restrictBinarized Q) :=
      restrictBinarized_sequenceClosed G Q hQ
    have hsubSource :
        ∀ A,
          SequenceLeastLanguage G A ⊆
            restrictBinarized Q A := by
      intro A u hu
      exact hu (restrictBinarized Q) hRestr
    have hIntoRestr :
        w ∈ binarizedInterpretation
          (restrictBinarized Q) X :=
      binarizedInterpretation_mono hsubSource X hcanonical
    exact
      binarizedInterpretation_restrict_subset
        G Q hQ X hIntoRestr

/-- BinaryNullableGrammar presentation of the binarized sequence grammar. -/
def binarizedBinaryGrammar
    (G : SequenceGrammar N α) :
    BinaryNullableGrammar (BinarizedState N) α :=
  sequenceToBinaryNullableGrammar
    (binarizedSequenceGrammar G)

/--
For every binary state, explicit binary derivability is exactly the canonical
binarized interpretation of the source least language.
-/
theorem binarizedBinary_derives_iff_canonical
    (G : SequenceGrammar N α)
    (X : BinarizedState N)
    (w : List α) :
    BinaryNullableDerives (binarizedBinaryGrammar G) X w
      ↔
    w ∈ binarizedInterpretation
      (SequenceLeastLanguage G) X := by
  calc
    BinaryNullableDerives (binarizedBinaryGrammar G) X w
        ↔
      w ∈ SequenceLeastLanguage
        (binarizedSequenceGrammar G) X :=
      binaryNullableDerives_iff_sequenceLeast
        (binarizedSequenceGrammar G)
        (binarizedSequenceGrammar_binaryForm G)
        X w
    _ ↔
      w ∈ binarizedInterpretation
        (SequenceLeastLanguage G) X := by
      rw [binarization_leastLanguage_all_eq G X]

/-- In particular, old states preserve the source least-generated language. -/
theorem binarizedBinary_old_language_eq
    (G : SequenceGrammar N α)
    (A : N) :
    {w | BinaryNullableDerives
      (binarizedBinaryGrammar G)
      (BinarizedState.old A) w}
      =
    SequenceLeastLanguage G A := by
  apply Set.ext
  intro w
  change
    BinaryNullableDerives
        (binarizedBinaryGrammar G)
        (BinarizedState.old A) w
      ↔
    w ∈ SequenceLeastLanguage G A
  calc
    BinaryNullableDerives
        (binarizedBinaryGrammar G)
        (BinarizedState.old A) w
      ↔
    w ∈ binarizedInterpretation
      (SequenceLeastLanguage G)
      (BinarizedState.old A) :=
        binarizedBinary_derives_iff_canonical
          G (BinarizedState.old A) w
    _ ↔ w ∈ SequenceLeastLanguage G A := by
      rfl

end SequenceBinaryGrammarBridge

end TCS1
end LeanCfgProject
