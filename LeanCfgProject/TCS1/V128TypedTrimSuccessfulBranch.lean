import LeanCfgProject.TCS1.V128RetainedTypedLanguageEquality

/-!
# TCS #1 v128: successful typed branch survives productive/reachable trim

This is the exact generic trimming bridge needed by the E_n D witness
of Proposition `prop:typed-thickness-gap`: a typed binary derivation
whose parent is a start child puts both typed children on a successful
typed start derivation. Both children remain active after trimming,
and their displayed successful derivations restrict to the reduced CFG.

The remaining gap-example proof must instantiate these premises with
the explicit G_n source rules and its fixed typing h_c.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section SuccessfulBranch

variable {α : Type u} {M : Type v} {N : Type w}
variable [Monoid M] [Fintype M]

/-- A successful typed binary production immediately below a start child
    retains both children in the concrete typed refinement. -/
theorem typedStartBinary_children_survive_trim
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    {A B C : N} {μ ν : M} {wB wC : Word α}
    (hstart : startRule A)
    (hbin : binaryRule A B C)
    (dB : TypedDerives H terminalRule binaryRule (B, μ) wB)
    (dC : TypedDerives H terminalRule binaryRule (C, ν) wC) :
    ConcreteTypedActive H terminalRule binaryRule startRule (B, μ) ∧
      ConcreteTypedActive H terminalRule binaryRule startRule (C, ν) := by
  have dA : TypedDerives H terminalRule binaryRule
      (A, μ * ν) (wB ++ wC) :=
    TypedDerives.binary hbin dB dC
  have hparent : ConcreteTypedActive H terminalRule binaryRule
      startRule (A, μ * ν) :=
    ProductiveTypedReachable.start hstart ⟨wB ++ wC, dA⟩
  exact ⟨ProductiveTypedReachable.left hparent hbin
    ⟨wB, dB⟩ ⟨wC, dC⟩,
    ProductiveTypedReachable.right hparent hbin
    ⟨wB, dB⟩ ⟨wC, dC⟩⟩

/-- The successful child derivations themselves survive trimming as well. -/
theorem typedStartBinary_children_derivations_survive_trim
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    {A B C : N} {μ ν : M} {wB wC : Word α}
    (hstart : startRule A)
    (hbin : binaryRule A B C)
    (dB : TypedDerives H terminalRule binaryRule (B, μ) wB)
    (dC : TypedDerives H terminalRule binaryRule (C, ν) wC) :
    ReducedTypedDerives H terminalRule binaryRule
        (ConcreteTypedActive H terminalRule binaryRule startRule)
        (B, μ) wB ∧
      ReducedTypedDerives H terminalRule binaryRule
        (ConcreteTypedActive H terminalRule binaryRule startRule)
        (C, ν) wC := by
  obtain ⟨hB, hC⟩ :=
    typedStartBinary_children_survive_trim H terminalRule binaryRule
      startRule hstart hbin dB dC
  let trim := concreteTypedActive_trimClosure
    H terminalRule binaryRule startRule
  exact ⟨trim.restrict hB dB, trim.restrict hC dC⟩

end SuccessfulBranch

end TCS1
end LeanCfgProject
