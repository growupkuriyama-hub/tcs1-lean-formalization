import LeanCfgProject.TCS1.WitnessSetConstruction

/-!
# TCS #1 v63: reducedness produces the canonical witness choices

The witness-set construction in the previous module used a
ReducedWitnessChoices interface.  This file derives that interface from the
two qualitative properties supplied by trimming the full yield-typed
refinement:

* productivity of every surviving typed nonterminal;
* reachability of every surviving typed nonterminal by a terminal context.

For typed symbols which are direct children of the start symbol, the empty
context is chosen.  This mirrors the manuscript's minimal-context argument:
the empty context has total length zero and is therefore the canonical choice.

The result removes another abstract hypothesis from the completeness theorem.
No quantitative minimality or shortlex machinery is needed here; those become
relevant only in the characteristic-data size bounds.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section ReducednessChoices

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

variable {H : FixedFiniteMonoidHom α M}
variable {terminalRule : N → α → Prop}
variable {binaryRule : N → N → N → Prop}
variable {startRule : N → Prop}
variable {epsilonStart : Prop}
variable {Active : N × M → Prop}

/-- A productive terminal yield of one typed nonterminal. -/
structure ProductiveYield
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop)
    (X : N × M) where
  word : Word α
  derives :
    ReducedTypedDerives H terminalRule binaryRule Active X word

/--
A terminal reaching context for one typed nonterminal.
Replacing X by any terminal yield derived from X still gives a target word.
-/
structure TerminalReachingContext
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (X : N × M) where
  left : Word α
  right : Word α
  plug :
    ∀ {z : Word α},
      ReducedTypedDerives H terminalRule binaryRule Active X z →
      ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart Active
        (left ++ z ++ right)

/--
Qualitative reducedness certificate for the surviving part of the typed
refinement.  It is exactly the logical content of productivity plus
reachability needed by the finite-witness proof.
-/
structure QualitativeReducedness
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop) where
  productive :
    ∀ X, Active X →
      Nonempty
        (ProductiveYield H terminalRule binaryRule Active X)

  reachable :
    ∀ X, Active X →
      Nonempty
        (TerminalReachingContext
          H terminalRule binaryRule startRule epsilonStart Active X)

/--
A direct start child has the empty terminal reaching context.
-/
def startChildReachingContext
    (A : N) (μ : M)
    (hstart : startRule A)
    (hactive : Active (A, μ)) :
    TerminalReachingContext
      H terminalRule binaryRule startRule epsilonStart Active (A, μ) where
  left := []
  right := []
  plug := by
    intro z d
    change
      ReducedTypedStartDerives
        H terminalRule binaryRule startRule epsilonStart Active
        ([] ++ z ++ [])
    simpa using
      (ReducedTypedStartDerives.nonempty hstart hactive d)

/--
For an inactive pair there can be no reduced typed derivation, so an arbitrary
empty context satisfies the reaching-context implication vacuously.
-/
def inactiveReachingContext
    (X : N × M)
    (hX : ¬ Active X) :
    TerminalReachingContext
      H terminalRule binaryRule startRule epsilonStart Active X where
  left := []
  right := []
  plug := by
    intro z d
    exact False.elim
      (hX
        (reducedTypedDerives_active
          H terminalRule binaryRule Active d))

/-- Chosen productive yield, arbitrary off the active part. -/
noncomputable def chosenProductiveYield
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M) :
    Word α := by
  classical
  by_cases hX : Active X
  · exact (Classical.choice (R.productive X hX)).word
  · exact []

theorem chosenProductiveYield_derives
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M)
    (hX : Active X) :
    ReducedTypedDerives
      H terminalRule binaryRule Active X
      (chosenProductiveYield R X) := by
  classical
  simp only [chosenProductiveYield, dif_pos hX]
  exact (Classical.choice (R.productive X hX)).derives

/--
Chosen reaching context.  Direct start children are deliberately assigned the
empty context; every other active pair uses a reaching witness from reducedness.
-/
noncomputable def chosenReachingContext
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M) :
    TerminalReachingContext
      H terminalRule binaryRule startRule epsilonStart Active X := by
  classical
  by_cases hX : Active X
  · by_cases hs : startRule X.1
    · exact startChildReachingContext X.1 X.2 hs hX
    · exact Classical.choice (R.reachable X hX)
  · exact inactiveReachingContext X hX

theorem chosenReachingContext_start_empty
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (A : N) (μ : M)
    (hstart : startRule A)
    (hactive : Active (A, μ)) :
    (chosenReachingContext R (A, μ)).left = [] ∧
      (chosenReachingContext R (A, μ)).right = [] := by
  classical
  simp [chosenReachingContext, hactive, hstart, startChildReachingContext]

/--
Every qualitative reducedness certificate canonically supplies the interface
consumed by the finite witness construction.
-/
noncomputable def reducedWitnessChoices_of_reducedness
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active) :
    ReducedWitnessChoices
      H terminalRule binaryRule startRule epsilonStart Active := by
  classical
  refine
    { omega := chosenProductiveYield R
      left := fun X => (chosenReachingContext R X).left
      right := fun X => (chosenReachingContext R X).right
      omegaDerives := ?_
      reaches := ?_
      start_empty := ?_ }
  · intro X hX
    exact chosenProductiveYield_derives R X hX
  · intro X hX z d
    exact (chosenReachingContext R X).plug d
  · intro A μ hstart hactive
    exact chosenReachingContext_start_empty R A μ hstart hactive

/--
Completeness directly from qualitative reducedness and inclusion of the
explicit finite witness language.
-/
theorem completeness_of_qualitative_reducedness
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (hWK :
      CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart Active
          (reducedWitnessChoices_of_reducedness R) ⊆
        (↑K : Set (Word α))) :
    ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart Active ⊆
      BatchLanguage H K := by
  exact
    canonicalWitnessWords_completeness
      H K terminalRule binaryRule startRule epsilonStart Active
      (reducedWitnessChoices_of_reducedness R) hWK

/--
Exact finite-sample reconstruction directly from qualitative reducedness.
This is the abstract Lean counterpart of combining the reduced typed
refinement, its finite witness set, soundness, and completeness.
-/
theorem exact_reconstruction_of_qualitative_reducedness
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (R :
      QualitativeReducedness
        H terminalRule binaryRule startRule epsilonStart Active)
    (L : Set (Word α))
    (hTarget :
      ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart Active = L)
    (hWK :
      CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart Active
          (reducedWitnessChoices_of_reducedness R) ⊆
        (↑K : Set (Word α)))
    (hK : (↑K : Set (Word α)) ⊆ L)
    (hsub : FixedHSubstitutable H L) :
    BatchLanguage H K = L := by
  apply Set.Subset.antisymm
  · exact batchLanguage_sound H K L hK hsub
  · rw [← hTarget]
    exact
      completeness_of_qualitative_reducedness
        H K terminalRule binaryRule startRule epsilonStart Active R hWK

end ReducednessChoices

end TCS1
end LeanCfgProject
