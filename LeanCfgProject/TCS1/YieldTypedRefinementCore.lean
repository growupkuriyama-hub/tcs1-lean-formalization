import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v63: yield-typed refinement core

This module formalizes the algebraic kernel of Proposition 5.2
("typed lifting and yield invariant") in the v63 manuscript.

We model the non-start SSBNF fragment by terminal rules A -> a and binary
rules A -> B C.  The yield-typed refinement replaces A by pairs (A, mu),
uses type h([a]) at terminal leaves, and multiplies child types at binary
nodes.

The verified statements are:

* every untyped derivation lifts to a typed derivation indexed by h(yield);
* every typed derivation erases to an untyped derivation;
* every typed derivation has the advertised yield type;
* the type of a fixed typed derivation yield is unique.

This is the proof kernel needed before adding reducedness/trimming, canonical
witnesses, and the completeness simulation.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section YieldTypedRefinement

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/--
Untyped derivations for the non-start SSBNF fragment:
terminal rules and binary rules only.
-/
inductive UntypedDerives
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop) :
    N → Word α → Prop
  | terminal {A : N} {a : α} :
      terminalRule A a →
      UntypedDerives terminalRule binaryRule A [a]
  | binary {A B C : N} {wB wC : Word α} :
      binaryRule A B C →
      UntypedDerives terminalRule binaryRule B wB →
      UntypedDerives terminalRule binaryRule C wC →
      UntypedDerives terminalRule binaryRule A (wB ++ wC)

/--
Yield-typed derivations.  The nonterminal component records the underlying
symbol and the fixed-h yield type.
-/
inductive TypedDerives
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop) :
    (N × M) → Word α → Prop
  | terminal {A : N} {a : α} :
      terminalRule A a →
      TypedDerives H terminalRule binaryRule (A, H.h [a]) [a]
  | binary
      {A B C : N}
      {μ ν : M}
      {wB wC : Word α} :
      binaryRule A B C →
      TypedDerives H terminalRule binaryRule (B, μ) wB →
      TypedDerives H terminalRule binaryRule (C, ν) wC →
      TypedDerives H terminalRule binaryRule (A, μ * ν) (wB ++ wC)

/-- Every non-start SSBNF derivation has a nonempty terminal yield. -/
theorem untypedDerives_length_pos
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w) :
    0 < w.length := by
  induction d with
  | terminal hterm =>
      simp
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      simp only [List.length_append]
      omega

/-- Typed non-start derivations also have nonempty terminal yields. -/
theorem typedDerives_length_pos
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {X : N × M}
    {w : Word α}
    (d : TypedDerives H terminalRule binaryRule X w) :
    0 < w.length := by
  induction d with
  | terminal hterm =>
      simp
  | @binary A B C μ ν wB wC hbin dB dC ihB ihC =>
      simp only [List.length_append]
      omega

/-- Erasing type annotations sends a typed derivation to an untyped one. -/
theorem typedDerives_erase
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {X : N × M}
    {w : Word α}
    (d : TypedDerives H terminalRule binaryRule X w) :
    UntypedDerives terminalRule binaryRule X.1 w := by
  induction d with
  | terminal hterm =>
      exact UntypedDerives.terminal hterm
  | binary hbin _dB _dC ihB ihC =>
      exact UntypedDerives.binary hbin ihB ihC

/--
Every untyped derivation lifts canonically by annotating each node with the
h-type of its terminal yield.
-/
theorem untypedDerives_lift
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w) :
    TypedDerives H terminalRule binaryRule (A, H.h w) w := by
  induction d with
  | terminal hterm =>
      exact TypedDerives.terminal hterm
  | @binary A B C wB wC hbin _dB _dC ihB ihC =>
      have htyped :
          TypedDerives H terminalRule binaryRule
            (A, H.h wB * H.h wC) (wB ++ wC) :=
        TypedDerives.binary hbin ihB ihC
      rw [H.map_append wB wC]
      exact htyped

/--
Yield invariant from Proposition 5.2:
a typed non-start derivation indexed by mu can derive only words of h-type mu.
-/
theorem typedDerives_yield_type_general
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {X : N × M}
    {w : Word α}
    (d : TypedDerives H terminalRule binaryRule X w) :
    H.h w = X.2 := by
  induction d with
  | terminal _hterm =>
      rfl
  | @binary A B C μ ν wB wC _hbin _dB _dC ihB ihC =>
      rw [H.map_append wB wC, ihB, ihC]

/-- Specialized form of the yield invariant for a named typed symbol. -/
theorem typedDerives_yield_type
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {μ : M}
    {w : Word α}
    (d : TypedDerives H terminalRule binaryRule (A, μ) w) :
    H.h w = μ := by
  exact typedDerives_yield_type_general H terminalRule binaryRule d

/--
The untyped derivation relation is exactly the projection of the full
yield-typed relation.
-/
theorem untypedDerives_iff_exists_typed
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α} :
    UntypedDerives terminalRule binaryRule A w ↔
      ∃ μ : M, TypedDerives H terminalRule binaryRule (A, μ) w := by
  constructor
  · intro d
    exact ⟨H.h w, untypedDerives_lift H terminalRule binaryRule d⟩
  · rintro ⟨μ, d⟩
    exact typedDerives_erase H terminalRule binaryRule d

/-- A word has at most one type in the yield-typed refinement. -/
theorem typedDerives_type_unique
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {μ ν : M}
    {w : Word α}
    (dμ : TypedDerives H terminalRule binaryRule (A, μ) w)
    (dν : TypedDerives H terminalRule binaryRule (A, ν) w) :
    μ = ν := by
  calc
    μ = H.h w := (typedDerives_yield_type H terminalRule binaryRule dμ).symm
    _ = ν := typedDerives_yield_type H terminalRule binaryRule dν

end YieldTypedRefinement

end TCS1
end LeanCfgProject
