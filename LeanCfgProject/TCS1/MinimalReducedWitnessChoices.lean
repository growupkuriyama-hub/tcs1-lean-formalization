import LeanCfgProject.TCS1.FixedWindowLemma72Facade
import LeanCfgProject.TCS1.ReducednessWitnessChoices

/-!
# TCS #1 v68: minimum-length canonical witness choices

Section 7 chooses a canonical typed yield omega(X) and a canonical terminal
reaching context chi(X).  For the characteristic-data length estimates, only
their minimum-length properties are used; the secondary shortlex tie-break is
irrelevant to every numerical inequality.

This file constructs those minimum-length choices from qualitative reducedness
using well-ordering of Nat.  It therefore removes the abstract
`CanonicalChoiceMinimality` assumption from the quantitative facade.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section MinimalReducedWitnessChoices

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

variable {H : FixedFiniteMonoidHom α M}
variable {terminalRule : N → α → Prop}
variable {binaryRule : N → N → N → Prop}
variable {startRule : N → Prop}
variable {epsilonStart : Prop}
variable {Active : N × M → Prop}

/-- Lengths realized by productive reduced typed yields of X. -/
def ProductiveYieldLength
    (X : N × M)
    (n : Nat) : Prop :=
  ∃ P : ProductiveYield
      H terminalRule binaryRule Active X,
    P.word.length = n

/-- Total context lengths realized by terminal reaching contexts of X. -/
def ReachingContextLength
    (X : N × M)
    (n : Nat) : Prop :=
  ∃ C : TerminalReachingContext
      H terminalRule binaryRule startRule epsilonStart Active X,
    C.left.length + C.right.length = n

/-- Every active symbol realizes at least one productive-yield length. -/
theorem exists_productiveYieldLength
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M)
    (hX : Active X) :
    ∃ n : Nat, ProductiveYieldLength
      (H := H) (terminalRule := terminalRule)
      (binaryRule := binaryRule) (Active := Active)
      X n := by
  obtain ⟨P⟩ := R.productive X hX
  exact ⟨P.word.length, P, rfl⟩

/-- Every active symbol realizes at least one terminal-context length. -/
theorem exists_reachingContextLength
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M)
    (hX : Active X) :
    ∃ n : Nat, ReachingContextLength
      (H := H) (terminalRule := terminalRule)
      (binaryRule := binaryRule) (startRule := startRule)
      (epsilonStart := epsilonStart) (Active := Active)
      X n := by
  obtain ⟨C⟩ := R.reachable X hX
  exact ⟨C.left.length + C.right.length, C, rfl⟩

/-- A productive yield realizing the least possible terminal-word length. -/
noncomputable def minimumProductiveYield
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M)
    (hX : Active X) :
    ProductiveYield H terminalRule binaryRule Active X := by
  classical
  let hex :=
    exists_productiveYieldLength
      (H := H) (terminalRule := terminalRule)
      (binaryRule := binaryRule) (startRule := startRule)
      (epsilonStart := epsilonStart) (Active := Active)
      R X hX
  exact Classical.choose (Nat.find_spec hex)

/-- The chosen productive yield is no longer than any other productive yield. -/
theorem minimumProductiveYield_length_le
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M)
    (hX : Active X)
    (P : ProductiveYield
      H terminalRule binaryRule Active X) :
    (minimumProductiveYield R X hX).word.length ≤
      P.word.length := by
  classical
  let hex :=
    exists_productiveYieldLength
      (H := H) (terminalRule := terminalRule)
      (binaryRule := binaryRule) (startRule := startRule)
      (epsilonStart := epsilonStart) (Active := Active)
      R X hX
  have hchosen :
      (minimumProductiveYield R X hX).word.length =
        Nat.find hex := by
    exact Classical.choose_spec (Nat.find_spec hex)
  rw [hchosen]
  exact
    Nat.find_min' hex
      ⟨P, rfl⟩

/-- A terminal reaching context realizing the least possible total length. -/
noncomputable def minimumReachingContext
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M)
    (hX : Active X) :
    TerminalReachingContext
      H terminalRule binaryRule startRule epsilonStart Active X := by
  classical
  let hex :=
    exists_reachingContextLength
      (H := H) (terminalRule := terminalRule)
      (binaryRule := binaryRule) (startRule := startRule)
      (epsilonStart := epsilonStart) (Active := Active)
      R X hX
  exact Classical.choose (Nat.find_spec hex)

/-- The chosen reaching context has least total terminal-context length. -/
theorem minimumReachingContext_length_le
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M)
    (hX : Active X)
    (C : TerminalReachingContext
      H terminalRule binaryRule startRule epsilonStart Active X) :
    (minimumReachingContext R X hX).left.length +
        (minimumReachingContext R X hX).right.length ≤
      C.left.length + C.right.length := by
  classical
  let hex :=
    exists_reachingContextLength
      (H := H) (terminalRule := terminalRule)
      (binaryRule := binaryRule) (startRule := startRule)
      (epsilonStart := epsilonStart) (Active := Active)
      R X hX
  have hchosen :
      (minimumReachingContext R X hX).left.length +
          (minimumReachingContext R X hX).right.length =
        Nat.find hex := by
    exact Classical.choose_spec (Nat.find_spec hex)
  rw [hchosen]
  exact
    Nat.find_min' hex
      ⟨C, rfl⟩

/-- Minimum-length productive word, arbitrary off the active part. -/
noncomputable def minimumProductiveWord
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M) :
    Word α := by
  classical
  by_cases hX : Active X
  · exact (minimumProductiveYield R X hX).word
  · exact []

/-- Minimum-length reaching context, vacuous off the active part. -/
noncomputable def minimumContext
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M) :
    TerminalReachingContext
      H terminalRule binaryRule startRule epsilonStart Active X := by
  classical
  by_cases hX : Active X
  · exact minimumReachingContext R X hX
  · exact inactiveReachingContext X hX

/--
Qualitative reducedness supplies witness choices whose productive yield and
reaching context are minimum-length.
-/
noncomputable def minimalReducedWitnessChoices_of_reducedness
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active) :
    ReducedWitnessChoices
      H terminalRule binaryRule startRule epsilonStart Active := by
  classical
  refine
    { omega := minimumProductiveWord R
      left := fun X => (minimumContext R X).left
      right := fun X => (minimumContext R X).right
      omegaDerives := ?_
      reaches := ?_
      start_empty := ?_ }
  · intro X hX
    simp only [minimumProductiveWord, dif_pos hX]
    exact (minimumProductiveYield R X hX).derives
  · intro X hX z d
    exact (minimumContext R X).plug d
  · intro A μ hstart hactive
    let C0 :=
      startChildReachingContext
        (H := H) (terminalRule := terminalRule)
        (binaryRule := binaryRule) (startRule := startRule)
        (epsilonStart := epsilonStart) (Active := Active)
        A μ hstart hactive
    have hminRaw :=
      minimumReachingContext_length_le
        R (A, μ) hactive C0
    have hmin :
        (minimumReachingContext R (A, μ) hactive).left.length +
            (minimumReachingContext R (A, μ) hactive).right.length ≤ 0 := by
      change
        (minimumReachingContext R (A, μ) hactive).left.length +
            (minimumReachingContext R (A, μ) hactive).right.length ≤ 0
        at hminRaw
      exact hminRaw
    have hleftLen :
        (minimumReachingContext R (A, μ) hactive).left.length = 0 := by
      omega
    have hrightLen :
        (minimumReachingContext R (A, μ) hactive).right.length = 0 := by
      omega
    have hleft :
        (minimumReachingContext R (A, μ) hactive).left = [] := by
      simpa using hleftLen
    have hright :
        (minimumReachingContext R (A, μ) hactive).right = [] := by
      simpa using hrightLen
    simp only [minimumContext, dif_pos hactive]
    exact ⟨hleft, hright⟩

/--
The minimum-length choices satisfy exactly the quantitative minimality
interface consumed by Lemma 7.2.
-/
theorem minimalReducedWitnessChoices_minimality
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active) :
    CanonicalChoiceMinimality
      H terminalRule binaryRule startRule epsilonStart Active
      (minimalReducedWitnessChoices_of_reducedness R) := by
  classical
  constructor
  · intro X hX z dz
    let P : ProductiveYield
        H terminalRule binaryRule Active X :=
      { word := z
        derives := dz }
    have hmin :=
      minimumProductiveYield_length_le
        R X hX P
    simpa [minimalReducedWitnessChoices_of_reducedness,
      minimumProductiveWord, hX] using hmin
  · intro X hX left right hplug
    let C : TerminalReachingContext
        H terminalRule binaryRule startRule epsilonStart Active X :=
      { left := left
        right := right
        plug := hplug }
    have hmin :=
      minimumReachingContext_length_le
        R X hX C
    simpa [minimalReducedWitnessChoices_of_reducedness,
      minimumContext, hX] using hmin

end MinimalReducedWitnessChoices

end TCS1
end LeanCfgProject
