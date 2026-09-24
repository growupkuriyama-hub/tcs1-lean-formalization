import LeanCfgProject.TCS1.BinarizationKernel

/-!
# TCS #1 v65: full-language preservation of binarization

Appendix A first isolates terminals and then replaces every structural
right-hand side longer than two by a right-associated binary chain of fresh
suffix states. This file lifts the local suffix semantics from
`BinarizationKernel` to equality of the full generated languages.

Generated languages are presented denotationally as the least family of
terminal-word languages closed under all rules. The proof uses the canonical
interpretation in which an old state A denotes its source language and a fresh
suffix state [B_1,...,B_m] denotes the concatenation language of that block.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinarizationLeastClosed

variable {N : Type u}
variable {α : Type v}

/-- Grammar after terminal isolation: terminal rules plus nonterminal sequences. -/
structure SequenceGrammar (N : Type u) (α : Type v) where
  terminal : N → α → Prop
  structural : N → List N → Prop

/-- One rule application under a supplied interpretation of child states. -/
def SequenceRuleStepLanguage
    (G : SequenceGrammar N α)
    (L : N → Set (List α))
    (A : N) :
    Set (List α) :=
  {w |
    (∃ a, G.terminal A a ∧ w = [a]) ∨
    (∃ rhs, G.structural A rhs ∧ NTSequenceRealizes L rhs w)}

/-- A state-language family closed under all rules of a sequence grammar. -/
def SequenceGrammarClosed
    (G : SequenceGrammar N α)
    (L : N → Set (List α)) : Prop :=
  ∀ A, SequenceRuleStepLanguage G L A ⊆ L A

/-- Least generated language of one state. -/
def SequenceLeastLanguage
    (G : SequenceGrammar N α)
    (A : N) :
    Set (List α) :=
  {w | ∀ L, SequenceGrammarClosed G L → w ∈ L A}

/--
Top-level right-hand side after binarization. Lengths zero, one and two stay
literal; a longer sequence B C D ... becomes B followed by the fresh suffix
state for C D ....
-/
def topBinarizedRhs :
    List N → List (BinarizedState N)
  | [] => []
  | [B] => [BinarizedState.old B]
  | [B, C] => [BinarizedState.old B, BinarizedState.old C]
  | B :: C :: D :: rest =>
      [BinarizedState.old B,
       BinarizedState.suffix (C :: D :: rest)]

/-- Structural rules of the binary presentation. -/
inductive BinarizedStructuralRule
    (G : SequenceGrammar N α) :
    BinarizedState N → List (BinarizedState N) → Prop
  | source
      {A : N} {rhs : List N}
      (h : G.structural A rhs) :
      BinarizedStructuralRule G
        (BinarizedState.old A)
        (topBinarizedRhs rhs)
  | suffixEmpty :
      BinarizedStructuralRule G
        (BinarizedState.suffix [])
        []
  | suffixUnit
      (B : N) :
      BinarizedStructuralRule G
        (BinarizedState.suffix [B])
        [BinarizedState.old B]
  | suffixBinary
      (B C : N) :
      BinarizedStructuralRule G
        (BinarizedState.suffix [B, C])
        [BinarizedState.old B, BinarizedState.old C]
  | suffixLong
      (B C D : N) (rest : List N) :
      BinarizedStructuralRule G
        (BinarizedState.suffix (B :: C :: D :: rest))
        [BinarizedState.old B,
         BinarizedState.suffix (C :: D :: rest)]

/-- Binary grammar produced from a sequence grammar. -/
def binarizedSequenceGrammar
    (G : SequenceGrammar N α) :
    SequenceGrammar (BinarizedState N) α where
  terminal X a :=
    ∃ A, X = BinarizedState.old A ∧ G.terminal A a
  structural :=
    BinarizedStructuralRule G

/-- Restrict a binary-state interpretation to the old states. -/
def restrictBinarized
    (Q : BinarizedState N → Set (List α)) :
    N → Set (List α) :=
  fun A => Q (BinarizedState.old A)

/--
The top-level binary RHS realizes exactly the same terminal words as the
source nonterminal sequence under the canonical suffix interpretation.
-/
theorem topBinarizedRhs_realizes_iff
    (L : N → Set (List α))
    (rhs : List N)
    (w : List α) :
    NTSequenceRealizes L rhs w ↔
      NTSequenceRealizes
        (binarizedInterpretation L)
        (topBinarizedRhs rhs)
        w := by
  cases rhs with
  | nil =>
      simp [topBinarizedRhs, NTSequenceRealizes]
  | cons B rest =>
      cases rest with
      | nil =>
          simpa [topBinarizedRhs] using
            (ntSequence_old_map_iff L [B] w).symm
      | cons C rest₂ =>
          cases rest₂ with
          | nil =>
              constructor
              · intro h
                have hp :
                    BinaryPairRealizes L B C w :=
                  (ntSequence_two_iff_binaryPair L B C w).1 h
                exact
                  (ntSequence_two_iff_binaryPair
                    (binarizedInterpretation L)
                    (BinarizedState.old B)
                    (BinarizedState.old C)
                    w).2
                    ((binaryPair_old_iff L B C w).2 hp)
              · intro h
                have hp :
                    BinaryPairRealizes
                      (binarizedInterpretation L)
                      (BinarizedState.old B)
                      (BinarizedState.old C)
                      w :=
                  (ntSequence_two_iff_binaryPair
                    (binarizedInterpretation L)
                    (BinarizedState.old B)
                    (BinarizedState.old C)
                    w).1 h
                exact
                  (ntSequence_two_iff_binaryPair L B C w).2
                    ((binaryPair_old_iff L B C w).1 hp)
          | cons D tail =>
              calc
                NTSequenceRealizes L (B :: C :: D :: tail) w
                    ↔
                  BinaryPairRealizes
                    (binarizedInterpretation L)
                    (BinarizedState.old B)
                    (BinarizedState.suffix (C :: D :: tail))
                    w :=
                  first_binary_split_iff L B C (D :: tail) w
                _ ↔
                  NTSequenceRealizes
                    (binarizedInterpretation L)
                    [BinarizedState.old B,
                     BinarizedState.suffix (C :: D :: tail)]
                    w :=
                  (ntSequence_two_iff_binaryPair
                    (binarizedInterpretation L)
                    (BinarizedState.old B)
                    (BinarizedState.suffix (C :: D :: tail))
                    w).symm

/--
If the source interpretation is closed, its canonical suffix extension is
closed under every rule of the binary grammar.
-/
theorem binarizedInterpretation_sequenceClosed
    (G : SequenceGrammar N α)
    (L : N → Set (List α))
    (hclosed : SequenceGrammarClosed G L) :
    SequenceGrammarClosed
      (binarizedSequenceGrammar G)
      (binarizedInterpretation L) := by
  intro X w hw
  rcases hw with hterm | hstruct
  · rcases hterm with ⟨a, ⟨A, hX, hGa⟩, hw⟩
    subst X
    subst w
    change [a] ∈ L A
    exact hclosed A (Or.inl ⟨a, hGa, rfl⟩)
  · rcases hstruct with ⟨rhs, hrule, hreal⟩
    cases hrule with
    | @source A sourceRhs hG =>
        change w ∈ L A
        apply hclosed A
        right
        exact
          ⟨sourceRhs, hG,
            (topBinarizedRhs_realizes_iff
              L sourceRhs w).2 hreal⟩
    | suffixEmpty =>
        exact hreal
    | suffixUnit B =>
        exact
          (ntSequence_old_map_iff L [B] w).1 hreal
    | suffixBinary B C =>
        exact
          (ntSequence_old_map_iff L [B, C] w).1 hreal
    | suffixLong B C D rest =>
        have hp :
            BinaryPairRealizes
              (binarizedInterpretation L)
              (BinarizedState.old B)
              (BinarizedState.suffix (C :: D :: rest))
              w :=
          (ntSequence_two_iff_binaryPair
            (binarizedInterpretation L)
            (BinarizedState.old B)
            (BinarizedState.suffix (C :: D :: rest))
            w).1 hreal
        exact
          (first_binary_split_iff L B C (D :: rest) w).2 hp

/--
Embedding old states into an arbitrary binary interpretation is exactly the
same as realizing the source sequence in its restriction.
-/
theorem ntSequence_old_restrict_iff
    (Q : BinarizedState N → Set (List α))
    (xs : List N)
    (w : List α) :
    NTSequenceRealizes Q (xs.map BinarizedState.old) w
      ↔
    NTSequenceRealizes (restrictBinarized Q) xs w := by
  induction xs generalizing w with
  | nil =>
      simp [NTSequenceRealizes]
  | cons A rest ih =>
      simp [NTSequenceRealizes, restrictBinarized, ih]

/--
Every canonical suffix-language word belongs to the corresponding state of
any closed binary interpretation.
-/
theorem binarizedInterpretation_restrict_subset
    (G : SequenceGrammar N α)
    (Q : BinarizedState N → Set (List α))
    (hclosed :
      SequenceGrammarClosed
        (binarizedSequenceGrammar G) Q) :
    ∀ X,
      binarizedInterpretation (restrictBinarized Q) X ⊆ Q X := by
  intro X
  cases X with
  | old A =>
      intro w hw
      exact hw
  | suffix xs =>
      induction xs with
      | nil =>
          intro w hw
          apply hclosed (BinarizedState.suffix [])
          right
          exact
            ⟨[],
              BinarizedStructuralRule.suffixEmpty,
              hw⟩
      | cons B rest ih =>
          cases rest with
          | nil =>
              intro w hw
              apply hclosed (BinarizedState.suffix [B])
              right
              refine
                ⟨[BinarizedState.old B],
                  BinarizedStructuralRule.suffixUnit B,
                  ?_⟩
              exact
                (ntSequence_old_restrict_iff Q [B] w).2 hw
          | cons C rest₂ =>
              cases rest₂ with
              | nil =>
                  intro w hw
                  apply hclosed (BinarizedState.suffix [B, C])
                  right
                  refine
                    ⟨[BinarizedState.old B,
                       BinarizedState.old C],
                      BinarizedStructuralRule.suffixBinary B C,
                      ?_⟩
                  exact
                    (ntSequence_old_restrict_iff Q [B, C] w).2 hw
              | cons D tail =>
                  intro w hw
                  have hp :
                      BinaryPairRealizes
                        (binarizedInterpretation
                          (restrictBinarized Q))
                        (BinarizedState.old B)
                        (BinarizedState.suffix (C :: D :: tail))
                        w :=
                    (first_binary_split_iff
                      (restrictBinarized Q)
                      B C (D :: tail) w).1 hw
                  rcases hp with ⟨u, v, huv, hu, hv⟩
                  have hvQ :
                      v ∈ Q
                        (BinarizedState.suffix (C :: D :: tail)) :=
                    ih hv
                  have hpQ :
                      BinaryPairRealizes Q
                        (BinarizedState.old B)
                        (BinarizedState.suffix (C :: D :: tail))
                        w :=
                    ⟨u, v, huv, hu, hvQ⟩
                  apply hclosed
                    (BinarizedState.suffix (B :: C :: D :: tail))
                  right
                  exact
                    ⟨[BinarizedState.old B,
                       BinarizedState.suffix (C :: D :: tail)],
                      BinarizedStructuralRule.suffixLong
                        B C D tail,
                      (ntSequence_two_iff_binaryPair
                        Q
                        (BinarizedState.old B)
                        (BinarizedState.suffix (C :: D :: tail))
                        w).2 hpQ⟩

/--
Restricting an arbitrary closed binary interpretation to the old states gives
a closed interpretation of the source grammar.
-/
theorem restrictBinarized_sequenceClosed
    (G : SequenceGrammar N α)
    (Q : BinarizedState N → Set (List α))
    (hclosed :
      SequenceGrammarClosed
        (binarizedSequenceGrammar G) Q) :
    SequenceGrammarClosed G (restrictBinarized Q) := by
  intro A w hw
  rcases hw with hterm | hstruct
  · rcases hterm with ⟨a, hGa, hw⟩
    subst w
    apply hclosed (BinarizedState.old A)
    left
    exact ⟨a, ⟨A, rfl, hGa⟩, rfl⟩
  · rcases hstruct with ⟨rhs, hG, hreal⟩
    have hideal :
        NTSequenceRealizes
          (binarizedInterpretation (restrictBinarized Q))
          (topBinarizedRhs rhs)
          w :=
      (topBinarizedRhs_realizes_iff
        (restrictBinarized Q) rhs w).1 hreal
    have hsub :
        ∀ X,
          binarizedInterpretation (restrictBinarized Q) X ⊆ Q X :=
      binarizedInterpretation_restrict_subset G Q hclosed
    have hQreal :
        NTSequenceRealizes Q (topBinarizedRhs rhs) w :=
      ntSequenceRealizes_mono hsub hideal
    apply hclosed (BinarizedState.old A)
    right
    exact
      ⟨topBinarizedRhs rhs,
        BinarizedStructuralRule.source hG,
        hQreal⟩

/--
Binarization preserves the full least-generated language of every source
nonterminal.
-/
theorem binarization_leastLanguage_eq
    (G : SequenceGrammar N α)
    (A : N) :
    SequenceLeastLanguage
        (binarizedSequenceGrammar G)
        (BinarizedState.old A)
      =
    SequenceLeastLanguage G A := by
  apply Set.ext
  intro w
  constructor
  · intro hw L hL
    have hBin :
        SequenceGrammarClosed
          (binarizedSequenceGrammar G)
          (binarizedInterpretation L) :=
      binarizedInterpretation_sequenceClosed G L hL
    exact hw (binarizedInterpretation L) hBin
  · intro hw Q hQ
    have hRestr :
        SequenceGrammarClosed G (restrictBinarized Q) :=
      restrictBinarized_sequenceClosed G Q hQ
    exact hw (restrictBinarized Q) hRestr

end BinarizationLeastClosed

end TCS1
end LeanCfgProject
