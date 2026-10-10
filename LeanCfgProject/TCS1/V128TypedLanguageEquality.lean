import LeanCfgProject.TCS1.YieldTypedRefinementCore

/-!
# TCS #1 v128 typed non-start language equality

This is a new theorem-facing delta, not an exact v128 manuscript audit.
It strengthens the previously formalized yield-type invariant to the
extensional equality now stated in Proposition 5.2 of manuscript v128.

This file formalizes the untrimmed non-start SSBNF derivation fragment.
Identifying these languages with a concretely trimmed full grammar and its
start production remains a separate integration obligation.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section TypedLanguageEquality

variable {α : Type u} {M : Type v} {N : Type w}
variable [Monoid M] [Fintype M]

/-- Untyped non-start yield language of a grammar symbol. -/
def untypedNonstartLanguage
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (A : N) : Set (Word α) :=
  { w | UntypedDerives terminalRule binaryRule A w }

/-- Yield language of a symbol indexed by its finite-monoid type. -/
def typedNonstartLanguage
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (A : N) (μ : M) : Set (Word α) :=
  { w | TypedDerives H terminalRule binaryRule (A, μ) w }

/-- Exact equality of the typed non-start yield language with its h-fibre. -/
theorem typedNonstartLanguage_eq_inter_fiber
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (A : N) (μ : M) :
    typedNonstartLanguage H terminalRule binaryRule A μ =
      untypedNonstartLanguage terminalRule binaryRule A ∩
        {w : Word α | H.h w = μ} := by
  ext w
  constructor
  · intro hw
    have d : TypedDerives H terminalRule binaryRule (A, μ) w := hw
    exact ⟨typedDerives_erase H terminalRule binaryRule d,
      typedDerives_yield_type H terminalRule binaryRule d⟩
  · rintro ⟨hu, ht⟩
    have d : UntypedDerives terminalRule binaryRule A w := hu
    have hLift :
        TypedDerives H terminalRule binaryRule (A, H.h w) w :=
      untypedDerives_lift H terminalRule binaryRule d
    change TypedDerives H terminalRule binaryRule (A, μ) w
    rw [ht] at hLift
    exact hLift

end TypedLanguageEquality

end TCS1
end LeanCfgProject
