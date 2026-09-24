import LeanCfgProject.TCS1.FixedWindowTreeCombinatorics
import LeanCfgProject.TCS1.SSBNFThicknessBounds

/-!
# TCS #1: path-shortening bound for shortest nonempty yields

This module formalizes the combinatorial core of the appendix argument

  min{|w|>0 : A =>* w} <= 1 + |V_B| * tau_B.

After choosing one terminal leaf, the proof shortcuts repeated nonterminal
labels on the root-to-leaf path.  The shortened path therefore has no repeated
labels and hence at most |V_B| nonterminal occurrences.  At each path node,
the off-path sibling is replaced by a shortest terminal yield of length at
most tau_B; the chosen terminal leaf contributes one symbol.

The grammar-semantic fact that such shortcutting/replacement yields a valid
derivation is kept separate.  Here we verify the finite pigeonhole and length
arithmetic exactly.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section ShortestNonemptyPathBound

variable {N : Type u}

/--
A repetition-free path over a finite nonterminal type has length at most the
number of available nonterminal labels.
-/
theorem nodup_path_length_le_card
    [Fintype N] [DecidableEq N]
    (path : List N)
    (hnodup : path.Nodup) :
    path.length ≤ Fintype.card N := by
  have hsubset : path.toFinset ⊆ (Finset.univ : Finset N) :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup hnodup] at hcard
  simpa using hcard

/--
Off-path sibling replacements indexed by a shortened root-to-leaf path
contribute at most |V_B| * tau_B terminals.
-/
theorem sibling_replacement_sum_le
    [Fintype N] [DecidableEq N]
    (path : List N)
    (siblings : List Nat)
    (τB : Nat)
    (hnodup : path.Nodup)
    (hindex : siblings.length ≤ path.length)
    (heach : ∀ s ∈ siblings, s ≤ τB) :
    siblings.sum ≤ Fintype.card N * τB := by
  have hpath : path.length ≤ Fintype.card N :=
    nodup_path_length_le_card path hnodup
  exact chainExpansion_sum_le
    siblings
    (Fintype.card N)
    τB
    (le_trans hindex hpath)
    heach

/--
The chosen terminal leaf contributes one symbol, yielding the manuscript's
bound 1 + |V_B| * tau_B.
-/
theorem shortened_path_nonempty_yield_bound
    [Fintype N] [DecidableEq N]
    (path : List N)
    (siblings : List Nat)
    (τB : Nat)
    (hnodup : path.Nodup)
    (hindex : siblings.length ≤ path.length)
    (heach : ∀ s ∈ siblings, s ≤ τB) :
    1 + siblings.sum ≤ 1 + Fintype.card N * τB := by
  exact Nat.add_le_add_left
    (sibling_replacement_sum_le
      path siblings τB hnodup hindex heach)
    1

/--
If |V_B| and tau_B satisfy the linear bounds used earlier in the appendix,
the path-shortening estimate is bounded by the explicit quadratic SSBNF
thickness envelope.
-/
theorem shortened_path_le_ssbnfThicknessEnvelope
    [Fintype N] [DecidableEq N]
    (path : List N)
    (siblings : List Nat)
    (τB cV c₁ n τR : Nat)
    (hnodup : path.Nodup)
    (hindex : siblings.length ≤ path.length)
    (heach : ∀ s ∈ siblings, s ≤ τB)
    (hV : Fintype.card N ≤ cV * n)
    (hτ : τB ≤ binarizedThicknessEnvelope c₁ n τR) :
    1 + siblings.sum ≤
      ssbnfThicknessEnvelope cV c₁ n τR := by
  have hPath :
      1 + siblings.sum ≤ 1 + Fintype.card N * τB :=
    shortened_path_nonempty_yield_bound
      path siblings τB hnodup hindex heach
  have hEnvelope :
      1 + Fintype.card N * τB ≤
        ssbnfThicknessEnvelope cV c₁ n τR := by
    exact nullableNonemptyEnvelope_le_ssbnfThicknessEnvelope
      hV hτ
  exact le_trans hPath hEnvelope

end ShortestNonemptyPathBound

end TCS1
end LeanCfgProject
