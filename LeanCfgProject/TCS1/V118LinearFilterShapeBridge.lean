import LeanCfgProject.TCS1.V115SSBNFRegularIntersection
import LeanCfgProject.TCS1.LinearTypedShapeBridge

/-!
# TCS #1 v118: the linear-spine shape under finite-state filtering

The existing finite-DFA product proof gives exact SSBNF language intersection.
The additional assertion that regular filtering preserves linearity requires
spine-shape arguments: one wrapper child per binary rule, no binary rule
headed by a wrapper, and a terminal rule for every *productive* wrapper.

This module proves those statements, not yet the full arbitrary-linear-CFG
finite-presentation and trimming theorem.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V118LinearFilterShapeBridge

variable {α : Type u} {N : Type v} {Q : Type w}

/-- A source wrapper does not acquire binary rules in the DFA product. -/
theorem v118_filter_wrapper_no_binary
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Wrapper : N → Prop)
    (shape : UntypedLinearSpineShape terminalRule binaryRule Wrapper)
    {X Y Z : V115FilterState N Q}
    (hwrap : Wrapper X.1) :
    ¬ v115FilterBinary binaryRule X Y Z := by
  intro hb
  exact shape.wrapper_no_binary hwrap hb.1

/-- The DFA product preserves the single-wrapper-child binary shape. -/
theorem v118_filter_binary_linear_children
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Wrapper : N → Prop)
    (shape : UntypedLinearSpineShape terminalRule binaryRule Wrapper)
    {X Y Z : V115FilterState N Q}
    (hb : v115FilterBinary binaryRule X Y Z) :
    (Wrapper Y.1 ∧ ¬ Wrapper Z.1) ∨
      (¬ Wrapper Y.1 ∧ Wrapper Z.1) :=
  shape.binary_children hb.1

/-- Every successful product derivation from a wrapper is a terminal leaf. -/
theorem v118_filter_productive_wrapper_terminal
    (δ : Q → α → Q)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Wrapper : N → Prop)
    (shape : UntypedLinearSpineShape terminalRule binaryRule Wrapper)
    {X : V115FilterState N Q}
    (hwrap : Wrapper X.1)
    {w : Word α}
    (d : UntypedDerives
      (v115FilterTerminal δ terminalRule)
      (v115FilterBinary binaryRule)
      X w) :
    ∃ a : α, v115FilterTerminal δ terminalRule X a ∧ w = [a] := by
  cases d with
  | @terminal X letter ht =>
      exact ⟨letter, ht, rfl⟩
  | @binary A B C wB wC hb _ _ =>
      exact False.elim (shape.wrapper_no_binary hwrap hb.1)

end V118LinearFilterShapeBridge
end TCS1
end LeanCfgProject
