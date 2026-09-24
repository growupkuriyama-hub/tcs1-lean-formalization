import LeanCfgProject.TCS1.FixedWindowTreeSurgeryFacade
import LeanCfgProject.TCS1.CanonicalWitnessCompleteness

/-!
# TCS #1 v68: reduced-refinement facade for Lemma 7.1

The tree-surgery development constructs a successful derivation in the full
yield-typed refinement.  The manuscript then observes that, because the root
typed symbol is reachable and the reconstructed tree is successful, every
typed symbol on that tree survives the productive/reachable trimming.

This file isolates exactly that trimming step as a small certificate and uses
it to state the paper-facing bound for the canonical minimal yield of a
surviving typed nonterminal.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section FixedWindowLemma71ReducedFacade

variable {N : Type u}
variable {α : Type v}
variable {M : Type w} [Monoid M] [Fintype M]

/--
Semantic closure property of the productive/reachable trimmed typed
refinement.

Starting from an active root, every successful full typed derivation can be
viewed as a derivation in the trimmed refinement.  For the manuscript's
`Active`, this is the sentence "the tree is successful and the root is
reachable, hence all typed symbols on it survive trimming."
-/
structure SuccessfulTypedTrimClosure
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop) where
  restrict :
    ∀ {X : N × M} {word : Word α},
      Active X →
      TypedDerives H terminalRule binaryRule X word →
      ReducedTypedDerives
        H terminalRule binaryRule Active X word

/--
Exact reduced-refinement form of Lemma 7.1, modulo the explicit trimming
closure certificate above.

If `omega` is length-minimal among the reduced typed yields of a surviving
symbol, then its length is bounded by the manuscript quantity
`B_{k,l}(G)`.  A shortlex-minimal choice satisfies the displayed minimality
hypothesis automatically.
-/
theorem fixedWindow_reduced_minimal_typed_yield_length_le
    [Fintype N] [DecidableEq N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop)
    (trim :
      SuccessfulTypedTrimClosure
        H terminalRule binaryRule Active)
    {A : N}
    {μ : M}
    {omega : Word α}
    (dOmega :
      ReducedTypedDerives
        H terminalRule binaryRule Active
        (A, μ) omega)
    (hminimal :
      ∀ z : Word α,
        ReducedTypedDerives
          H terminalRule binaryRule Active
          (A, μ) z →
        omega.length ≤ z.length)
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ X : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule X z
          ∧ z.length ≤ τ) :
    omega.length ≤
      fixedWindowTypedYieldBound
        (k + l) (Fintype.card N) τ := by
  have dOmegaFull :
      TypedDerives H terminalRule binaryRule
        (A, μ) omega :=
    reducedTypedDerives_to_typedDerives
      H terminalRule binaryRule Active dOmega

  obtain ⟨z, dzFull, hz⟩ :=
    exists_fixedWindow_bounded_typed_yield
      H terminalRule binaryRule
      dOmegaFull k l hrespect τ hshort

  have hactive : Active (A, μ) :=
    reducedTypedDerives_active
      H terminalRule binaryRule Active dOmega

  have dzReduced :
      ReducedTypedDerives
        H terminalRule binaryRule Active
        (A, μ) z :=
    trim.restrict hactive dzFull

  exact le_trans (hminimal z dzReduced) hz

end FixedWindowLemma71ReducedFacade

end TCS1
end LeanCfgProject
