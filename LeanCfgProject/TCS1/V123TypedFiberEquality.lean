import LeanCfgProject.TCS1.ConcreteTypedTrimming
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage

/-!
# TCS #1 v123: fibre equality for each retained typed nonterminal

v123 strengthens the earlier yield-type invariant: if a non-start symbol
(A, μ) survives the productive-then-reachable typed trim, its generated
language is exactly the intersection of the original nonterminal language
L_G(A) with the h-fibre h⁻¹({μ}).

The earlier v88 formalization contained all ingredients, but did not package
this *precise v123 statement*. This file closes that theorem-level gap without
creating a new algorithm or weakening reducedness.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V123TypedFiberEquality

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Proof-bearing equivalence for an active typed state (A, μ). -/
theorem v123_retained_typed_derives_iff
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    {A : N} {μ : M}
    {word : Word α}
    (hactive :
      ConcreteTypedActive
        H terminalRule binaryRule startRule (A, μ)) :
    ReducedTypedDerives
        H terminalRule binaryRule
        (ConcreteTypedActive H terminalRule binaryRule startRule)
        (A, μ) word
      ↔
    (UntypedDerives terminalRule binaryRule A word ∧
      H.h word = μ) := by
  constructor
  · intro d
    exact
      ⟨typedDerives_erase
          H terminalRule binaryRule
          (reducedTypedDerives_to_typedDerives
            H terminalRule binaryRule
            (ConcreteTypedActive H terminalRule binaryRule startRule)
            d),
        reducedTypedDerives_yield_type
          H terminalRule binaryRule
          (ConcreteTypedActive H terminalRule binaryRule startRule)
          d⟩
  · rintro ⟨d, hμ⟩
    have dt :
        TypedDerives H terminalRule binaryRule
          (A, H.h word) word :=
      untypedDerives_lift H terminalRule binaryRule d
    rw [hμ] at dt
    exact
      (concreteTypedActive_trimClosure
        H terminalRule binaryRule startRule).restrict
        hactive dt

/-- Exact set equality L_tildeG(A_μ) = L_G(A) ∩ h⁻¹({μ})
for every non-start symbol retained by the corrected typed trim.
This is the additional v123 clause of Proposition 'typed lifting and yield invariant'. -/
theorem v123_retained_typed_fibre_language_eq
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (A : N)
    (μ : M)
    (hactive :
      ConcreteTypedActive
        H terminalRule binaryRule startRule (A, μ)) :
    {w : Word α |
      ReducedTypedDerives
        H terminalRule binaryRule
        (ConcreteTypedActive H terminalRule binaryRule startRule)
        (A, μ) w} =
    {w : Word α |
      UntypedDerives terminalRule binaryRule A w}
      ∩
    {w : Word α | H.h w = μ} := by
  apply Set.ext
  intro word
  exact
    v123_retained_typed_derives_iff
      H terminalRule binaryRule startRule hactive

end V123TypedFiberEquality

end TCS1
end LeanCfgProject
