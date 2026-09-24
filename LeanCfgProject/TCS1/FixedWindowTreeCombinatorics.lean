import LeanCfgProject.TCS1.SSBNFThicknessBounds

/-!
# TCS #1: combinatorics behind bounded fixed-window typed yields

The proof of the fixed-window typed-yield lemma marks r=k+l boundary leaves,
takes the union of their root paths, shortens one-child chains until no
underlying nonterminal repeats, and then replaces omitted sibling subtrees by
shortest terminal yields.

This file isolates the finite combinatorics used in that argument:

* a full binary skeleton with r leaves has exactly 2r-1 vertices;
* if every suppressed one-child chain has length at most N, the expanded
  marked-path structure has at most (2r-1)N nonterminal occurrences;
* replacing at most that many omitted subtrees by yields of length at most
  tau contributes at most (2r-1)N*tau terminals.

No grammar semantics is hidden here: this is precisely the tree-counting
layer of the manuscript proof.
-/

namespace LeanCfgProject
namespace TCS1

section FixedWindowTreeCombinatorics

/-- Full binary skeleton obtained after suppressing maximal one-child chains. -/
inductive FullBinarySkeleton
  | leaf : FullBinarySkeleton
  | node : FullBinarySkeleton → FullBinarySkeleton → FullBinarySkeleton

namespace FullBinarySkeleton

/-- Number of marked leaves. -/
def leaves : FullBinarySkeleton → Nat
  | leaf => 1
  | node l r => leaves l + leaves r

/-- Total number of skeleton vertices, including marked leaves. -/
def vertices : FullBinarySkeleton → Nat
  | leaf => 1
  | node l r => vertices l + vertices r + 1

@[simp] theorem leaves_pos (T : FullBinarySkeleton) :
    0 < leaves T := by
  induction T with
  | leaf => simp [leaves]
  | node l r ihL ihR =>
      simp only [leaves]
      omega

/--
Exact full-binary-tree identity.  This formulation avoids subtraction:
vertices + 1 = 2 * leaves.
-/
theorem vertices_add_one_eq_two_mul_leaves
    (T : FullBinarySkeleton) :
    vertices T + 1 = 2 * leaves T := by
  induction T with
  | leaf =>
      simp [vertices, leaves]
  | node l r ihL ihR =>
      simp only [vertices, leaves]
      omega

/-- Equivalent paper-facing form: a skeleton with r leaves has 2r-1 vertices. -/
theorem vertices_eq_two_mul_leaves_sub_one
    (T : FullBinarySkeleton) :
    vertices T = 2 * leaves T - 1 := by
  have h := vertices_add_one_eq_two_mul_leaves T
  have hp := leaves_pos T
  omega

/--
If a skeleton has at most r marked leaves, it has at most 2r-1 vertices.
-/
theorem vertices_le_two_mul_bound_sub_one
    (T : FullBinarySkeleton)
    {r : Nat}
    (hleaves : leaves T ≤ r) :
    vertices T ≤ 2 * r - 1 := by
  have hEq := vertices_eq_two_mul_leaves_sub_one T
  have hpos := leaves_pos T
  omega

end FullBinarySkeleton

/--
Sum bound for the shortened one-child chains: if there are at most V skeleton
vertices and every chain has length at most N, the total number of retained
nonterminal occurrences is at most V*N.
-/
theorem chainExpansion_sum_le
    (chains : List Nat)
    (V N : Nat)
    (hcount : chains.length ≤ V)
    (heach : ∀ c ∈ chains, c ≤ N) :
    chains.sum ≤ V * N := by
  have hsum :
      chains.sum ≤ chains.length * N := by
    clear hcount
    induction chains with
    | nil =>
        simp
    | cons a t ih =>
        have ha : a ≤ N := heach a (by simp)
        have ht : ∀ c ∈ t, c ≤ N := by
          intro c hc
          exact heach c (by simp [hc])
        have hi := ih ht
        simp only [List.sum_cons, List.length_cons]
        calc
          a + t.sum ≤ N + t.length * N :=
            Nat.add_le_add ha hi
          _ = (t.length + 1) * N := by
            ring
  exact le_trans hsum (Nat.mul_le_mul_right N hcount)

/--
Specialized marked-path bound from the manuscript:
at most 2r-1 skeleton vertices, each expanded to at most N nonterminal nodes.
-/
theorem markedPath_nonterminal_count_le
    (chains : List Nat)
    (r N : Nat)
    (hvertices : chains.length ≤ 2 * r - 1)
    (heach : ∀ c ∈ chains, c ≤ N) :
    chains.sum ≤ (2 * r - 1) * N := by
  exact chainExpansion_sum_le chains (2 * r - 1) N hvertices heach

/--
If the number of omitted sibling subtrees is bounded by the retained marked
path size and each replacement yield has length at most tau, their total
terminal contribution is bounded accordingly.
-/
theorem omittedSibling_contribution_le
    {omitted retained N r τ : Nat}
    (hretained : retained ≤ (2 * r - 1) * N)
    (homitted : omitted ≤ retained) :
    omitted * τ ≤ (2 * r - 1) * N * τ := by
  exact Nat.mul_le_mul_right τ (le_trans homitted hretained)

/--
Final arithmetic line of the long-state case:
r marked boundary terminals plus omitted-sibling replacements.
-/
theorem fixedWindow_long_state_length_bound
    {boundary omitted retained N r τ : Nat}
    (hboundary : boundary = r)
    (hretained : retained ≤ (2 * r - 1) * N)
    (homitted : omitted ≤ retained) :
    boundary + omitted * τ ≤
      r + (2 * r - 1) * N * τ := by
  subst boundary
  exact Nat.add_le_add_left
    (omittedSibling_contribution_le hretained homitted)
    r

/--
Concrete composition with an actual full binary skeleton having exactly r
marked leaves and shortened chains indexed by its vertices.
-/
theorem skeleton_chain_bound
    (T : FullBinarySkeleton)
    (chains : List Nat)
    (N : Nat)
    (hindex : chains.length ≤ T.vertices)
    (heach : ∀ c ∈ chains, c ≤ N) :
    chains.sum ≤ (2 * T.leaves - 1) * N := by
  have hv :
      chains.length ≤ 2 * T.leaves - 1 := by
    rw [← T.vertices_eq_two_mul_leaves_sub_one]
    exact hindex
  exact markedPath_nonterminal_count_le chains T.leaves N hv heach

end FixedWindowTreeCombinatorics

end TCS1
end LeanCfgProject
