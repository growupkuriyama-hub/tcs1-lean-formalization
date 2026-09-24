import LeanCfgProject.TCS1.FixedWindowLemma71ReducedFacade

/-!
# TCS #1 v68: local closure criterion for successful trimming

Lemma 7.1 reconstructs a successful derivation in the full yield-typed
refinement.  To use minimality in the reduced refinement, that successful
derivation must survive trimming.

This file isolates a local sufficient condition.  Whenever an active parent
uses a binary rule in a successful typed derivation, the two actually used
typed children are active as well.  Under that condition, every successful
typed derivation rooted at an active symbol restricts recursively to a
`ReducedTypedDerives` proof.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section SuccessfulTypedTrimClosureBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/--
Local downward-closure property of the active part of a yield-typed grammar.

The child derivations are included in the premise because productivity of
their exact typed symbols is witnessed by those derivations; this is the form
satisfied by productive/reachable trimming.
-/
structure SuccessfulTypedTrimLocalClosure
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop) : Prop where
  binary_children :
    ∀ {A B C : N}
      {μ ν : M}
      {wB wC : Word α},
      binaryRule A B C →
      Active (A, μ * ν) →
      TypedDerives H terminalRule binaryRule
        (B, μ) wB →
      TypedDerives H terminalRule binaryRule
        (C, ν) wC →
      Active (B, μ) ∧ Active (C, ν)

/--
The local closure criterion recursively restricts every successful full typed
derivation rooted at an active symbol.
-/
theorem typedDerives_restrict_of_localClosure
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop)
    (hlocal :
      SuccessfulTypedTrimLocalClosure
        H terminalRule binaryRule Active)
    {X : N × M}
    {word : Word α}
    (d :
      TypedDerives H terminalRule binaryRule X word) :
    Active X →
    ReducedTypedDerives
      H terminalRule binaryRule Active X word := by
  induction d with
  | terminal hterm =>
      intro hactive
      exact
        ReducedTypedDerives.terminal
          hterm hactive
  | @binary A B C μ ν wB wC
      hbin dB dC ihB ihC =>
      intro hactive
      obtain ⟨hB, hC⟩ :=
        hlocal.binary_children
          hbin hactive dB dC
      exact
        ReducedTypedDerives.binary
          hbin hactive
          (ihB hB)
          (ihC hC)

/-- Local downward closure implies the trimming interface used by Lemma 7.1. -/
theorem successfulTypedTrimClosure_of_localClosure
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop)
    (hlocal :
      SuccessfulTypedTrimLocalClosure
        H terminalRule binaryRule Active) :
    SuccessfulTypedTrimClosure
      H terminalRule binaryRule Active where
  restrict := by
    intro X word hactive d
    exact
      typedDerives_restrict_of_localClosure
        H terminalRule binaryRule Active
        hlocal d hactive

end SuccessfulTypedTrimClosureBridge

end TCS1
end LeanCfgProject
