import LeanCfgProject.TCS1.V128TypedLanguageEquality
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage

/-!
# TCS #1 v128 Proposition 5.2: retained non-start symbol languages

For every non-start symbol (A, μ) retained by the concrete productive-
then-reachable typed trim, its *reduced* language equals the untyped
language of A intersected with the h-fibre of μ.

This is stronger than the untrimmed equality in
V128TypedLanguageEquality.lean and uses the already machine-checked
ConcreteTypedActive_trimClosure, not an ad-hoc trimming assumption.

The full reduced start-language equality was previously checked in
ConcreteTypedTrimLanguage.lean (concreteTypedActive_language_eq_untyped).
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section RetainedTypedEquality

variable {α : Type u} {M : Type v} {N : Type w}
variable [Monoid M] [Fintype M]

/-- Terminal language of a retained symbol in the concretely trimmed typing. -/
def retainedTypedNonstartLanguage
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (A : N) (μ : M) : Set (Word α) :=
  {w | ReducedTypedDerives H terminalRule binaryRule
    (ConcreteTypedActive H terminalRule binaryRule startRule)
    (A, μ) w}

/-- Exact v128 Proposition 5.2 equality for every retained non-start symbol. -/
theorem retainedTypedNonstartLanguage_eq_inter_fiber
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (A : N) (μ : M)
    (hactive : ConcreteTypedActive H terminalRule binaryRule startRule
      (A, μ)) :
    retainedTypedNonstartLanguage H terminalRule binaryRule startRule A μ =
      untypedNonstartLanguage terminalRule binaryRule A ∩
        {w : Word α | H.h w = μ} := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    have dReduced :
        ReducedTypedDerives H terminalRule binaryRule
          (ConcreteTypedActive H terminalRule binaryRule startRule)
          (A, μ) w := hw
    have dFull := reducedTypedDerives_to_typedDerives
      H terminalRule binaryRule
      (ConcreteTypedActive H terminalRule binaryRule startRule)
      dReduced
    exact ⟨typedDerives_erase H terminalRule binaryRule dFull,
      typedDerives_yield_type H terminalRule binaryRule dFull⟩
  · rintro ⟨hw, htype⟩
    change ReducedTypedDerives H terminalRule binaryRule
      (ConcreteTypedActive H terminalRule binaryRule startRule)
      (A, μ) w
    have dUntyped : UntypedDerives terminalRule binaryRule A w := hw
    have dFull : TypedDerives H terminalRule binaryRule (A, μ) w := by
      have dLift : TypedDerives H terminalRule binaryRule
        (A, H.h w) w :=
        untypedDerives_lift H terminalRule binaryRule dUntyped
      rw [htype] at dLift
      exact dLift
    exact (concreteTypedActive_trimClosure
      H terminalRule binaryRule startRule).restrict hactive dFull

end RetainedTypedEquality

end TCS1
end LeanCfgProject
