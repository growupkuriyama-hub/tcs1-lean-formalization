import LeanCfgProject.TCS1.ShortestNonemptyPathBound
import LeanCfgProject.TCS1.SSBNFThicknessBounds

/-!
# TCS #1: dependency-path bound for fixed-window contexts and witnesses

The fixed-window context lemma chooses a shortest dependency-graph path from
a non-start child of a start rule to a typed nonterminal X.  A shortest path
repeats no typed nonterminal.  Hence, with Nt available typed nonterminals,
the path has at most Nt vertices (and at most Nt-1 binary steps).  Expanding
the off-path sibling at each binary step by a canonical typed yield of length
at most B contributes at most Nt*B terminals to the external context.

This module verifies that pigeonhole/sum argument and the three witness-length
cases (anchor, terminal rule, binary rule) leading to the common envelope

  (Nt + 2) * B + 1.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section FixedWindowContextPathBound

variable {X : Type u}

/--
A repetition-free dependency path has at most Nt vertices when the typed
nonterminal universe has cardinality Nt.
-/
theorem dependency_path_vertices_le
    [Fintype X] [DecidableEq X]
    (path : List X)
    (hnodup : path.Nodup) :
    path.length ≤ Fintype.card X :=
  nodup_path_length_le_card path hnodup

/--
Sibling expansions along a shortest dependency path contribute at most Nt*B
terminals to the reaching context.
-/
theorem dependency_path_context_length_le
    [Fintype X] [DecidableEq X]
    (path : List X)
    (siblings : List Nat)
    (B : Nat)
    (hnodup : path.Nodup)
    (hsteps : siblings.length ≤ path.length)
    (hsibling : ∀ s ∈ siblings, s ≤ B) :
    siblings.sum ≤ Fintype.card X * B := by
  exact sibling_replacement_sum_le
    path siblings B hnodup hsteps hsibling

/--
Paper-facing version with an external numerical bound Nt on the typed
nonterminal count.
-/
theorem dependency_path_context_length_le_Nt
    [Fintype X] [DecidableEq X]
    (path : List X)
    (siblings : List Nat)
    (B Nt : Nat)
    (hnodup : path.Nodup)
    (hsteps : siblings.length ≤ path.length)
    (hsibling : ∀ s ∈ siblings, s ≤ B)
    (hNt : Fintype.card X ≤ Nt) :
    siblings.sum ≤ Nt * B := by
  have h0 :
      siblings.sum ≤ Fintype.card X * B :=
    dependency_path_context_length_le
      path siblings B hnodup hsteps hsibling
  exact le_trans h0 (Nat.mul_le_mul_right B hNt)

/--
Anchor witness: reaching context plus one canonical typed yield.
-/
theorem anchor_witness_length_le_common
    {context Nt B yieldLen : Nat}
    (hctx : context ≤ Nt * B)
    (hyield : yieldLen ≤ B) :
    context + yieldLen ≤ (Nt + 2) * B + 1 := by
  calc
    context + yieldLen
      ≤ Nt * B + B := Nat.add_le_add hctx hyield
    _ ≤ Nt * B + 2 * B + 1 := by omega
    _ = (Nt + 2) * B + 1 := by ring

/--
Terminal-rule witness: reaching context plus one terminal symbol.
-/
theorem terminal_witness_length_le_common
    {context Nt B : Nat}
    (hctx : context ≤ Nt * B) :
    context + 1 ≤ (Nt + 2) * B + 1 := by
  calc
    context + 1
      ≤ Nt * B + 1 := Nat.add_le_add_right hctx 1
    _ ≤ Nt * B + 2 * B + 1 := by omega
    _ = (Nt + 2) * B + 1 := by ring

/--
Binary-rule witness: reaching context plus two canonical typed yields.
-/
theorem binary_witness_length_le_common
    {context Nt B leftYield rightYield : Nat}
    (hctx : context ≤ Nt * B)
    (hleft : leftYield ≤ B)
    (hright : rightYield ≤ B) :
    context + leftYield + rightYield ≤ (Nt + 2) * B + 1 := by
  calc
    context + leftYield + rightYield
      ≤ Nt * B + B + B := by
        omega
    _ ≤ Nt * B + 2 * B + 1 := by omega
    _ = (Nt + 2) * B + 1 := by ring

/--
All three canonical witness families fit the same envelope used in the paper.
The tag 0/1/2 stands for anchor/terminal/binary; any other tag is harmlessly
bounded by the supplied direct hypothesis.
-/
theorem canonical_witness_common_envelope
    {Nt B context payload : Nat}
    (hctx : context ≤ Nt * B)
    (hpayload : payload ≤ 2 * B + 1) :
    context + payload ≤ (Nt + 2) * B + 1 := by
  calc
    context + payload
      ≤ Nt * B + (2 * B + 1) :=
        Nat.add_le_add hctx hpayload
    _ = (Nt + 2) * B + 1 := by ring

/--
Composition with the manuscript's fixed-window typed-yield bound.
-/
theorem fixedWindow_context_and_witness_bound
    [Fintype X] [DecidableEq X]
    (path : List X)
    (siblings : List Nat)
    (Nt r N τG : Nat)
    (hnodup : path.Nodup)
    (hsteps : siblings.length ≤ path.length)
    (hsibling :
      ∀ s ∈ siblings,
        s ≤ fixedWindowTypedYieldBound r N τG)
    (hNt : Fintype.card X ≤ Nt) :
    siblings.sum ≤
      Nt * fixedWindowTypedYieldBound r N τG ∧
    siblings.sum + (2 * fixedWindowTypedYieldBound r N τG + 1)
      ≤ fixedWindowWitnessLengthEnvelope Nt r N τG := by
  have hctx :
      siblings.sum ≤ Nt * fixedWindowTypedYieldBound r N τG :=
    dependency_path_context_length_le_Nt
      path siblings
      (fixedWindowTypedYieldBound r N τG)
      Nt
      hnodup hsteps hsibling hNt
  constructor
  · exact hctx
  · unfold fixedWindowWitnessLengthEnvelope
    exact canonical_witness_common_envelope hctx le_rfl

end FixedWindowContextPathBound

end TCS1
end LeanCfgProject
