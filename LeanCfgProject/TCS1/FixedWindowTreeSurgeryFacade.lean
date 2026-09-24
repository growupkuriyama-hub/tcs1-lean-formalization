import LeanCfgProject.TCS1.FixedWindowBoundaryMarking
import LeanCfgProject.TCS1.MarkedBoundaryNormalization
import LeanCfgProject.TCS1.MarkedBoundaryGapNormalization
import LeanCfgProject.TCS1.MarkedBoundaryExpansion
import LeanCfgProject.TCS1.SSBNFThicknessBounds

/-!
# TCS #1 v68: fixed-window tree-surgery facade

This module composes the three mechanical pieces of the long-word branch of
Lemma 7.1:

1. select the first k and last l terminal leaves;
2. cycle-shorten every maximal one-child chain;
3. replace omitted sibling subtrees by tau-short terminal yields.

The resulting theorem already gives the exact manuscript length envelope and a
genuine untyped derivation from the original nonterminal.

The only semantic fact intentionally left out of this facade is preservation
of the central fixed-window gap through cycle shortening.  Once that invariant
is transported from the ranked boundary kernel to the shortened kernel, the
existing FixedWindowBoundarySemantic layer lifts the derivation to the same
h_{k,l}-typed symbol.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section FixedWindowTreeSurgeryFacade

variable {N : Type u}
variable {α : Type v}

/--
Boundary selection followed by cycle shortening gives a kernel with exactly
k+l marked leaves and at most (2(k+l)-1)|N| omitted sibling subtrees.
-/
theorem exists_fixedWindow_cycle_shortened_kernel
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w.length) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedWord K' =
        w.take k ++ w.drop (w.length - l)
      ∧
      MarkedBoundaryKernel.markedLeafCount K' = k + l
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * (k + l) - 1) * Fintype.card N := by
  obtain ⟨K, hYield, hWord, hCount⟩ :=
    exists_fixedWindow_boundary_kernel
      terminalRule binaryRule d k l hr hfit
  obtain ⟨K', hCount', hWord', hOmit⟩ :=
    exists_cycle_shortened_kernel
      terminalRule binaryRule K
  refine ⟨K', ?_, ?_, ?_⟩
  · rw [hWord', hWord]
  · rw [hCount', hCount]
  · rw [hCount] at hOmit
    exact hOmit

/--
Boundary selection followed by gap-preserving cycle shortening.

In addition to the numerical bound, every omitted sibling remains in the
single central gap after the first k marked leaves.
-/
theorem exists_fixedWindow_cycle_shortened_kernel_ranked
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w.length) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedWord K' =
        w.take k ++ w.drop (w.length - l)
      ∧
      MarkedBoundaryKernel.markedLeafCount K' = k + l
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * (k + l) - 1) * Fintype.card N
      ∧
      MarkedBoundaryKernel.AllOmissionsAt K' k := by
  obtain ⟨K, hYield, hWord, hCount, hGap⟩ :=
    exists_fixedWindow_boundary_kernel_ranked
      terminalRule binaryRule d k l hr hfit
  obtain ⟨K', hCount', hWord', hOmit, hGap'⟩ :=
    exists_cycle_shortened_kernel_preserving_allOmissionsAt
      terminalRule binaryRule K k hGap
  refine ⟨K', ?_, ?_, ?_, hGap'⟩
  · rw [hWord', hWord]
  · rw [hCount', hCount]
  · rw [hCount] at hOmit
    exact hOmit

/--
Untyped long-word reconstruction with the exact Lemma 7.1 numerical bound.

This closes the combinatorial/derivational part of the long case.  The
remaining fixed-window obligation is solely that the shortened reconstruction
still places every replacement between the preserved prefix and suffix.
-/
theorem exists_fixedWindow_shortened_reconstruction
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w.length)
    (τ : Nat)
    (hshort :
      ∀ X : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule X z
          ∧ z.length ≤ τ) :
    ∃ w' : Word α,
      UntypedDerives terminalRule binaryRule A w'
      ∧
      w'.length ≤
        (k + l) +
          (2 * (k + l) - 1) * Fintype.card N * τ := by
  obtain ⟨K', hWord, hCount, hOmit⟩ :=
    exists_fixedWindow_cycle_shortened_kernel
      terminalRule binaryRule d k l hr hfit
  obtain ⟨w', d', hlen⟩ :=
    MarkedBoundaryKernel.exists_rebuilt_short_yield
      terminalRule binaryRule τ hshort K'
  have hmul :
      MarkedBoundaryKernel.omittedCount K' * τ ≤
        ((2 * (k + l) - 1) * Fintype.card N) * τ :=
    Nat.mul_le_mul_right τ hOmit
  rw [hCount] at hlen
  refine ⟨w', d', ?_⟩
  exact le_trans hlen
    (Nat.add_le_add_left hmul (k + l))

end FixedWindowTreeSurgeryFacade

section FixedWindowTypedLongCompletion

variable {N : Type u}
variable {α : Type v}
variable {M : Type w} [Monoid M] [Fintype M]

/--
Full typed long-word branch of Lemma 7.1.

The first/last boundary marking, gap-preserving cycle shortening, explicit
short sibling replacement, fixed-window type preservation, and the exact
length envelope are composed in one theorem.
-/
theorem exists_fixedWindow_long_typed_yield
    [Fintype N] [DecidableEq N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w₀ : Word α}
    (d₀ :
      UntypedDerives terminalRule binaryRule A w₀)
    {μ : M}
    (href : H.h w₀ = μ)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w₀.length)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ X : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule X z
          ∧ z.length ≤ τ) :
    ∃ w' : Word α,
      TypedDerives H terminalRule binaryRule
        (A, μ) w'
      ∧
      w'.length ≤
        (k + l) +
          (2 * (k + l) - 1) *
            Fintype.card N * τ := by
  obtain ⟨K', hMarked, hMarks, hOmit, hGap⟩ :=
    exists_fixedWindow_cycle_shortened_kernel_ranked
      terminalRule binaryRule d₀ k l hr hfit

  have hk :
      k ≤ MarkedBoundaryKernel.markedLeafCount K' := by
    rw [hMarks]
    omega

  obtain ⟨blocks, dAssembly, hCount, hEach⟩ :=
    exists_rebuilt_short_boundaryAssembly
      terminalRule binaryRule τ hshort
      K' k hk hGap

  let p : Word α := w₀.take k
  let q : Word α := w₀.drop (w₀.length - l)

  have hp : p.length = k := by
    dsimp [p]
    exact fixedWindow_prefix_length w₀ k l hfit

  have hq : q.length = l := by
    dsimp [q]
    exact fixedWindow_suffix_length w₀ k l hfit

  have hTake :
      (MarkedBoundaryKernel.markedWord K').take k = p := by
    rw [hMarked]
    dsimp [p, q]
    exact
      take_append_of_prefix_length
        (w₀.take k)
        (w₀.drop (w₀.length - l))
        k
        (fixedWindow_prefix_length w₀ k l hfit)

  have hDrop :
      (MarkedBoundaryKernel.markedWord K').drop k = q := by
    rw [hMarked]
    dsimp [p, q]
    exact
      drop_append_of_prefix_length
        (w₀.take k)
        (w₀.drop (w₀.length - l))
        k
        (fixedWindow_prefix_length w₀ k l hfit)

  rw [hTake, hDrop] at dAssembly

  obtain ⟨middle, hDecomp⟩ :=
    exists_fixedWindow_middle w₀ k l hfit

  have href' :
      H.h (p ++ middle ++ q) = μ := by
    rw [← hDecomp]
    exact href

  exact
    fixedWindow_long_typed_yield_of_reconstruction
      H terminalRule binaryRule
      hr hrespect
      p q middle blocks hp hq href'
      dAssembly
      (Fintype.card N) τ
      (MarkedBoundaryKernel.omittedCount K')
      (le_of_eq hCount)
      hOmit
      hEach

end FixedWindowTypedLongCompletion

section FixedWindowLemma71Facade

variable {N : Type u}
variable {α : Type v}
variable {M : Type w} [Monoid M] [Fintype M]

/--
Existential form of Lemma 7.1 for one productive typed non-start symbol.

The bound is exactly the manuscript quantity
`B_{k,l}(G)=tau` at r=0 and
`r+(2r-1)|N|tau` at r>0.
-/
theorem exists_fixedWindow_bounded_typed_yield
    [Fintype N] [DecidableEq N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {μ : M}
    {w₀ : Word α}
    (d₀ :
      TypedDerives H terminalRule binaryRule
        (A, μ) w₀)
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ X : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule X z
          ∧ z.length ≤ τ) :
    ∃ w' : Word α,
      TypedDerives H terminalRule binaryRule
        (A, μ) w'
      ∧
      w'.length ≤
        fixedWindowTypedYieldBound
          (k + l) (Fintype.card N) τ := by
  by_cases hr0 : k + l = 0
  · have hk : k = 0 := by omega
    have hl : l = 0 := by omega
    subst k
    subst l
    obtain ⟨z, dz, hz⟩ := hshort A
    have hwpos :
        0 < w₀.length :=
      typedDerives_length_pos
        H terminalRule binaryRule d₀
    have hzpos :
        0 < z.length :=
      untypedDerives_length_pos
        terminalRule binaryRule dz
    have hsame :
        H.h z = H.h w₀ :=
      zero_type_eq_of_respectsFixedWindowSummary
        H hrespect hzpos hwpos
    have href :
        H.h w₀ = μ :=
      typedDerives_yield_type
        H terminalRule binaryRule d₀
    have htype :
        H.h z = μ :=
      hsame.trans href
    have dzTyped :
        TypedDerives H terminalRule binaryRule
          (A, μ) z := by
      have dzLift :=
        untypedDerives_lift
          H terminalRule binaryRule dz
      simpa [htype] using dzLift
    refine ⟨z, dzTyped, ?_⟩
    simpa using hz

  · have hr : 0 < k + l := by
      omega
    by_cases hshortRef : w₀.length < k + l
    · refine ⟨w₀, d₀, ?_⟩
      rw [fixedWindowTypedYieldBound_of_pos hr]
      omega
    · have hfit : k + l ≤ w₀.length := by
        omega
      have dUntyped :
          UntypedDerives terminalRule binaryRule A w₀ :=
        typedDerives_erase
          H terminalRule binaryRule d₀
      have href :
          H.h w₀ = μ :=
        typedDerives_yield_type
          H terminalRule binaryRule d₀
      obtain ⟨w', d', hlen⟩ :=
        exists_fixedWindow_long_typed_yield
          H terminalRule binaryRule
          dUntyped href
          k l hr hfit hrespect τ hshort
      refine ⟨w', d', ?_⟩
      rw [fixedWindowTypedYieldBound_of_pos hr]
      exact hlen

/--
Paper-facing length statement for a canonical minimal typed yield.

Any length-minimal typed yield—and therefore in particular the manuscript's
shortlex-minimal `omega(X)`—is bounded by `B_{k,l}(G)`.
-/
theorem fixedWindow_minimal_typed_yield_length_le
    [Fintype N] [DecidableEq N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {μ : M}
    {omega : Word α}
    (dOmega :
      TypedDerives H terminalRule binaryRule
        (A, μ) omega)
    (hminimal :
      ∀ z : Word α,
        TypedDerives H terminalRule binaryRule
          (A, μ) z →
        omega.length ≤ z.length)
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ X : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule X z
          ∧ z.length ≤ τ) :
    omega.length ≤
      fixedWindowTypedYieldBound
        (k + l) (Fintype.card N) τ := by
  obtain ⟨z, dz, hz⟩ :=
    exists_fixedWindow_bounded_typed_yield
      H terminalRule binaryRule
      dOmega k l hrespect τ hshort
  exact le_trans (hminimal z dz) hz

end FixedWindowLemma71Facade

end TCS1
end LeanCfgProject
