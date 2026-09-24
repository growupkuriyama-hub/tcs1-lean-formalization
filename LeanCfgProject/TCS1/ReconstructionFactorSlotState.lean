import LeanCfgProject.TCS1.ReconstructionFiniteCandidateSpaces
import LeanCfgProject.TCS1.ReconstructionCFGPresentation
import Mathlib.Tactic

/-!
# TCS #1 v79: computable occurrence-slot representation of reconstruction states

The semantic bridge above used the subtype of observed paper-facing symbols
`[x;u,v]`.  For the final executable learner we instead use the already
finite and computable two-cut occurrence space `ReconstructionFactorSlot K`
itself as the nonterminal type.

A slot stores a sampled word and two cuts.  Decoding gives

  u = prefix before the first cut,
  x = factor between the cuts,
  v = suffix after the second cut.

Invalid/reversed cuts simply decode to an empty factor and will receive no
grammar rules later.  Every genuinely observed nonterminal has a canonical
slot, and the decoder recovers its triple exactly.  Thus this type gives a
computable finite state enumeration with the quadratic cardinality bound
already proved in `ReconstructionFiniteCandidateSpaces`.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section ReconstructionFactorSlotState

variable {α : Type u}
variable [DecidableEq α]

/-- Decode one sampled two-cut slot into the paper-facing triple [x;u,v]. -/
def reconstructionFactorSlotNonterminal
    {K : Finset (Word α)}
    (s : ReconstructionFactorSlot K) :
    ReconstructionNonterminal α :=
  let w := s.1.1
  let i := s.2.1.1
  let j := s.2.2.1
  ⟨(w.drop i).take (j - i),
    w.take i,
    w.drop j⟩

/-- Canonical two-cut slot corresponding to one observed occurrence uxv in K. -/
def observedReconstructionFactorSlot
    (K : Finset (Word α))
    {x u v : Word α}
    (hobs : Observed K x u v) :
    ReconstructionFactorSlot K := by
  let w : Word α := u ++ x ++ v
  have hw : w ∈ K := by
    simpa [w] using hobs.2
  have hi :
      u.length < w.length + 1 := by
    simp [w]
  have hj :
      u.length + x.length < w.length + 1 := by
    simp [w]
  exact
    ⟨⟨w, hw⟩,
      (⟨u.length, hi⟩,
       ⟨u.length + x.length, hj⟩)⟩

/-- Decoding the canonical slot returns exactly the observed triple. -/
theorem reconstructionFactorSlotNonterminal_observed
    (K : Finset (Word α))
    {x u v : Word α}
    (hobs : Observed K x u v) :
    reconstructionFactorSlotNonterminal
        (observedReconstructionFactorSlot K hobs)
      =
    (⟨x, u, v⟩ : ReconstructionNonterminal α) := by
  apply ReconstructionNonterminal.ext <;>
    simp [reconstructionFactorSlotNonterminal,
      observedReconstructionFactorSlot]

/-- The canonical observed slot therefore decodes to a nonempty factor. -/
theorem observedReconstructionFactorSlot_factor_ne_nil
    (K : Finset (Word α))
    {x u v : Word α}
    (hobs : Observed K x u v) :
    (reconstructionFactorSlotNonterminal
      (observedReconstructionFactorSlot K hobs)).factor ≠ [] := by
  rw [reconstructionFactorSlotNonterminal_observed]
  exact hobs.1

end ReconstructionFactorSlotState

end TCS1
end LeanCfgProject
