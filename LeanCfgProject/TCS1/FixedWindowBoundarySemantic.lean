import LeanCfgProject.TCS1.YieldTypedRefinementCore
import LeanCfgProject.TCS1.FixedWindowTreeCombinatorics
import LeanCfgProject.TCS1.FixedWindowSummarySemantic

/-!
# TCS #1 v68: fixed-window boundary-preservation semantic kernel

Lemma 7.1 of the v68 manuscript shortens a derivation tree while preserving
the first k and last l marked terminal leaves.  After the marked-path
shortcuts, omitted sibling subtrees are replaced by short terminal yields.
The resulting word therefore has the same fixed-window boundary summary and
the same h_{k,l}-type.

This module isolates the word-level semantic part of that argument.

* `concatBlocks` concatenates replacement sibling yields.
* `boundaryAssembly` inserts those blocks between a fixed prefix and suffix.
* `BoundaryTyping` abstracts the defining long-word property of h_{k,l}:
  once the boundary prefix/suffix are fixed, replacing the middle preserves
  type.
* the reconstructed word keeps that type;
* if it is still derivable from the same underlying nonterminal, the generic
  yield-typed lifting theorem lifts it to the prescribed typed symbol; and
* the actual reconstructed word length is bounded by the same
  r + (2r-1) N tau envelope as the manuscript.

The remaining grammar-tree obligation is therefore sharply separated:
construct a derivable `boundaryAssembly` after marked-path shortcutting and
sibling replacement.  No boundary/type or length arithmetic remains hidden in
that step.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section FixedWindowBoundarySemantic

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Concatenate a list of terminal blocks. -/
def concatBlocks : List (Word α) → Word α
  | [] => []
  | b :: bs => b ++ concatBlocks bs

@[simp] theorem concatBlocks_nil :
    concatBlocks ([] : List (Word α)) = [] := rfl

@[simp] theorem concatBlocks_cons
    (b : Word α)
    (bs : List (Word α)) :
    concatBlocks (b :: bs) = b ++ concatBlocks bs := rfl

/-- Length of the concatenated replacement blocks. -/
theorem concatBlocks_length
    (blocks : List (Word α)) :
    (concatBlocks blocks).length =
      (blocks.map (fun b => b.length)).sum := by
  induction blocks with
  | nil =>
      simp [concatBlocks]
  | cons b bs ih =>
      simp [concatBlocks, ih]

/-- Assemble a word with fixed left/right boundary and replaceable middle blocks. -/
def boundaryAssembly
    (p q : Word α)
    (blocks : List (Word α)) : Word α :=
  p ++ concatBlocks blocks ++ q

/-- Exact length of a boundary-preserving assembly. -/
theorem boundaryAssembly_length
    (p q : Word α)
    (blocks : List (Word α)) :
    (boundaryAssembly p q blocks).length =
      p.length +
        (blocks.map (fun b => b.length)).sum +
        q.length := by
  simp [boundaryAssembly, concatBlocks_length, Nat.add_assoc]

/--
Abstract long-word fixed-window property.

For the concrete h_{k,l}, this is exactly the statement that two long words
with the same length-k prefix and length-l suffix have the same type.
We formulate it using an explicit decomposition p ++ middle ++ q, which is the
shape produced by the marked-boundary derivation surgery.
-/
def BoundaryTyping
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat) : Prop :=
  ∀ (p q : Word α),
    p.length = k →
    q.length = l →
    ∀ m₁ m₂ : Word α,
      H.h (p ++ m₁ ++ q) =
        H.h (p ++ m₂ ++ q)

/--
The concrete fixed-window summary contract from Proposition 3.2 supplies the
abstract BoundaryTyping property needed below whenever k+l>0.
-/
theorem boundaryTyping_of_respectsFixedWindowSummary
    (H : FixedFiniteMonoidHom α M)
    {k l : Nat}
    (hr : 0 < k + l)
    (hrespect : RespectsFixedWindowSummary H k l) :
    BoundaryTyping H k l := by
  intro p q hp hq m₁ m₂
  exact
    boundary_type_eq_of_respectsFixedWindowSummary
      H hr hrespect p q m₁ m₂ hp hq

/-- Replacing the middle blocks preserves the fixed boundary type. -/
theorem boundaryAssembly_type_eq
    (H : FixedFiniteMonoidHom α M)
    {k l : Nat}
    (hBoundary : BoundaryTyping H k l)
    (p q : Word α)
    (hp : p.length = k)
    (hq : q.length = l)
    (blocks₁ blocks₂ : List (Word α)) :
    H.h (boundaryAssembly p q blocks₁) =
      H.h (boundaryAssembly p q blocks₂) := by
  exact
    hBoundary p q hp hq
      (concatBlocks blocks₁)
      (concatBlocks blocks₂)

/--
Paper-facing form: if a reference word p ++ middle ++ q has type mu, then
every boundary-preserving assembly has type mu.
-/
theorem boundaryAssembly_has_reference_type
    (H : FixedFiniteMonoidHom α M)
    {k l : Nat}
    (hBoundary : BoundaryTyping H k l)
    (p q middle : Word α)
    (blocks : List (Word α))
    (hp : p.length = k)
    (hq : q.length = l)
    {μ : M}
    (href : H.h (p ++ middle ++ q) = μ) :
    H.h (boundaryAssembly p q blocks) = μ := by
  have hsame :
      H.h (boundaryAssembly p q blocks) =
        H.h (boundaryAssembly p q [middle]) := by
    exact
      boundaryAssembly_type_eq
        H hBoundary p q hp hq blocks [middle]
  have hsingle :
      boundaryAssembly p q [middle] =
        p ++ middle ++ q := by
    simp [boundaryAssembly, concatBlocks]
  rw [hsingle] at hsame
  exact hsame.trans href

/--
Typed lifting after the boundary-preserving tree surgery.

Once the transformed word is still an untyped derivation from A and its
boundary gives the prescribed type mu, Proposition 5.2's generic lifting
theorem produces a derivation from the typed symbol (A,mu).
-/
theorem boundaryAssembly_typed_lift
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {k l : Nat}
    (hBoundary : BoundaryTyping H k l)
    (p q middle : Word α)
    (blocks : List (Word α))
    (hp : p.length = k)
    (hq : q.length = l)
    {A : N}
    {μ : M}
    (href : H.h (p ++ middle ++ q) = μ)
    (d :
      UntypedDerives terminalRule binaryRule A
        (boundaryAssembly p q blocks)) :
    TypedDerives H terminalRule binaryRule
      (A, μ) (boundaryAssembly p q blocks) := by
  have htype :
      H.h (boundaryAssembly p q blocks) = μ :=
    boundaryAssembly_has_reference_type
      H hBoundary p q middle blocks hp hq href
  have hd :
      TypedDerives H terminalRule binaryRule
        (A, H.h (boundaryAssembly p q blocks))
        (boundaryAssembly p q blocks) :=
    untypedDerives_lift
      H terminalRule binaryRule d
  simpa [htype] using hd

/--
Direct fixed-window version of the typed-lifting theorem, with the abstract
BoundaryTyping hypothesis discharged by the h_{k,l} summary contract.
-/
theorem boundaryAssembly_typed_lift_of_fixedWindowSummary
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {k l : Nat}
    (hr : 0 < k + l)
    (hrespect : RespectsFixedWindowSummary H k l)
    (p q middle : Word α)
    (blocks : List (Word α))
    (hp : p.length = k)
    (hq : q.length = l)
    {A : N}
    {μ : M}
    (href : H.h (p ++ middle ++ q) = μ)
    (d :
      UntypedDerives terminalRule binaryRule A
        (boundaryAssembly p q blocks)) :
    TypedDerives H terminalRule binaryRule
      (A, μ) (boundaryAssembly p q blocks) := by
  exact
    boundaryAssembly_typed_lift
      H terminalRule binaryRule
      (boundaryTyping_of_respectsFixedWindowSummary
        H hr hrespect)
      p q middle blocks hp hq href d

/--
Short-word branch of Lemma 7.1.

If x is a short reference word of type mu and a typed symbol (A,mu) derives
some y, summary reflection forces y=x.  Thus the short type has exactly the
reference yield.
-/
theorem fixedWindow_short_typed_yield_unique
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {k l : Nat}
    (hreflect : ReflectsFixedWindowSummary H k l)
    {A : N}
    {μ : M}
    {x y : Word α}
    (hx : x.length < fixedWindowThreshold k l)
    (href : H.h x = μ)
    (d :
      TypedDerives H terminalRule binaryRule
        (A, μ) y) :
    y = x ∧
      TypedDerives H terminalRule binaryRule
        (A, μ) x := by
  have hy : H.h y = μ :=
    typedDerives_yield_type
      H terminalRule binaryRule d
  have hxy : H.h x = H.h y :=
    href.trans hy.symm
  have heq : y = x :=
    short_word_unique_of_type
      H hreflect hx hxy
  constructor
  · exact heq
  · simpa [heq] using d

/-- Sum of actual replacement-block lengths under a uniform block bound. -/
theorem concatBlocks_length_le
    (blocks : List (Word α))
    (V τ : Nat)
    (hcount : blocks.length ≤ V)
    (heach : ∀ b ∈ blocks, b.length ≤ τ) :
    (concatBlocks blocks).length ≤ V * τ := by
  rw [concatBlocks_length]
  apply
    chainExpansion_sum_le
      (blocks.map (fun b => b.length))
      V τ
  · simpa using hcount
  · intro c hc
    rcases List.mem_map.mp hc with ⟨b, hb, rfl⟩
    exact heach b hb

/--
Semantic length version of the long-state estimate.

The prefix and suffix together account for exactly r marked boundary
terminals.  There are at most `retained` replacement blocks, and the marked
tree combinatorics bounds `retained` by (2r-1)N.  If every replacement block
has length at most tau, the assembled word satisfies the v68 Lemma 7.1 bound.
-/
theorem boundaryAssembly_fixedWindow_length_le
    (p q : Word α)
    (blocks : List (Word α))
    (r N τ retained : Nat)
    (hboundary : p.length + q.length = r)
    (hcount : blocks.length ≤ retained)
    (hretained : retained ≤ (2 * r - 1) * N)
    (heach : ∀ b ∈ blocks, b.length ≤ τ) :
    (boundaryAssembly p q blocks).length ≤
      r + (2 * r - 1) * N * τ := by
  have hmiddle :
      (concatBlocks blocks).length ≤ retained * τ :=
    concatBlocks_length_le
      blocks retained τ hcount heach
  have hretMul :
      retained * τ ≤ ((2 * r - 1) * N) * τ :=
    Nat.mul_le_mul_right τ hretained
  have hmiddle' :
      (concatBlocks blocks).length ≤
        ((2 * r - 1) * N) * τ :=
    le_trans hmiddle hretMul
  have hlen :
      (boundaryAssembly p q blocks).length =
        p.length + (concatBlocks blocks).length + q.length := by
    simp [boundaryAssembly, Nat.add_assoc]
  rw [hlen]
  calc
    p.length + (concatBlocks blocks).length + q.length
        =
      (p.length + q.length) +
        (concatBlocks blocks).length := by
          ring
    _ = r + (concatBlocks blocks).length := by
          rw [hboundary]
    _ ≤ r + ((2 * r - 1) * N) * τ :=
          Nat.add_le_add_left hmiddle' r

/--
The exact manuscript endpoint with r=k+l.
-/
theorem boundaryAssembly_fixedWindow_kl_length_le
    (p q : Word α)
    (blocks : List (Word α))
    (k l N τ retained : Nat)
    (hp : p.length = k)
    (hq : q.length = l)
    (hcount : blocks.length ≤ retained)
    (hretained : retained ≤ (2 * (k + l) - 1) * N)
    (heach : ∀ b ∈ blocks, b.length ≤ τ) :
    (boundaryAssembly p q blocks).length ≤
      (k + l) + (2 * (k + l) - 1) * N * τ := by
  apply
    boundaryAssembly_fixedWindow_length_le
      p q blocks (k + l) N τ retained
  · omega
  · exact hcount
  · exact hretained
  · exact heach

/--
Long-word semantic completion of Lemma 7.1.

Once the marked-tree surgery has supplied a derivable boundary assembly, a
bound on the number of retained replacement blocks, and a uniform bound tau
on every replacement yield, the fixed-window type and the manuscript length
bound follow automatically.
-/
theorem fixedWindow_long_typed_yield_of_reconstruction
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {k l : Nat}
    (hr : 0 < k + l)
    (hrespect : RespectsFixedWindowSummary H k l)
    (p q middle : Word α)
    (blocks : List (Word α))
    (hp : p.length = k)
    (hq : q.length = l)
    {A : N}
    {μ : M}
    (href : H.h (p ++ middle ++ q) = μ)
    (d :
      UntypedDerives terminalRule binaryRule A
        (boundaryAssembly p q blocks))
    (N τ retained : Nat)
    (hcount : blocks.length ≤ retained)
    (hretained :
      retained ≤ (2 * (k + l) - 1) * N)
    (heach : ∀ b ∈ blocks, b.length ≤ τ) :
    ∃ w' : Word α,
      TypedDerives H terminalRule binaryRule
        (A, μ) w'
      ∧
      w'.length ≤
        (k + l) + (2 * (k + l) - 1) * N * τ := by
  let w' : Word α :=
    boundaryAssembly p q blocks
  have htyped :
      TypedDerives H terminalRule binaryRule
        (A, μ) w' := by
    dsimp [w']
    exact
      boundaryAssembly_typed_lift_of_fixedWindowSummary
        H terminalRule binaryRule
        hr hrespect
        p q middle blocks hp hq href d
  have hlen :
      w'.length ≤
        (k + l) + (2 * (k + l) - 1) * N * τ := by
    dsimp [w']
    exact
      boundaryAssembly_fixedWindow_kl_length_le
        p q blocks k l N τ retained
        hp hq hcount hretained heach
  exact ⟨w', htyped, hlen⟩


end FixedWindowBoundarySemantic

end TCS1
end LeanCfgProject
