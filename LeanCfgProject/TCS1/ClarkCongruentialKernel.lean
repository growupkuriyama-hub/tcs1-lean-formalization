import LeanCfgProject.TCS1.YieldTypedRefinementCore

/-!
# TCS #1 v77: congruential comparison semantic kernel

Proposition 9.9 uses the yield-typed refinement to show that every surviving
typed nonterminal generates strings from one syntactic-congruence class of
the target language.

This file formalizes that semantic heart of the argument.  The later grammar
packaging step (removing the separated start symbol and using a finite initial
set) is intentionally kept separate.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section ClarkCongruentialKernel

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/--
Two yields of the same typed nonterminal are syntactically congruent whenever
they share a terminal reaching context in a fixed-h substitutable language.
-/
theorem typedYields_distribution_eq_of_shared_reachingContext
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (L : Set (Word α))
    (hsub : FixedHSubstitutable H L)
    {A : N} {μ : M}
    {x y u v : Word α}
    (dx :
      TypedDerives H terminalRule binaryRule
        (A, μ) x)
    (dy :
      TypedDerives H terminalRule binaryRule
        (A, μ) y)
    (hxL : u ++ x ++ v ∈ L)
    (hyL : u ++ y ++ v ∈ L) :
    Distribution L x = Distribution L y := by
  have hxne : x ≠ [] :=
    List.ne_nil_of_length_pos
      (typedDerives_length_pos
        H terminalRule binaryRule dx)
  have hyne : y ≠ [] :=
    List.ne_nil_of_length_pos
      (typedDerives_length_pos
        H terminalRule binaryRule dy)
  have htype : H.h x = H.h y := by
    calc
      H.h x = μ :=
        typedDerives_yield_type
          H terminalRule binaryRule dx
      _ = H.h y :=
        (typedDerives_yield_type
          H terminalRule binaryRule dy).symm
  exact
    hsub hxne hyne htype
      ⟨u, v, hxL, hyL⟩

/--
Paper-facing form: if one terminal context reaches a typed nonterminal and
embeds every one of its yields into L, then all of its yields lie in one
syntactic-congruence class of L.
-/
theorem typedNonterminal_single_distribution_class
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (L : Set (Word α))
    (hsub : FixedHSubstitutable H L)
    {A : N} {μ : M}
    (u v : Word α)
    (hreaches :
      ∀ w : Word α,
        TypedDerives H terminalRule binaryRule
          (A, μ) w →
        u ++ w ++ v ∈ L) :
    ∀ x y : Word α,
      TypedDerives H terminalRule binaryRule
        (A, μ) x →
      TypedDerives H terminalRule binaryRule
        (A, μ) y →
      Distribution L x = Distribution L y := by
  intro x y dx dy
  exact
    typedYields_distribution_eq_of_shared_reachingContext
      H terminalRule binaryRule L hsub
      dx dy (hreaches x dx) (hreaches y dy)

end ClarkCongruentialKernel

end TCS1
end LeanCfgProject
