import LeanCfgProject.TCS1.V115LocalConsequences

/-!
# TCS #1 v115: local-trivial characteristic data from ordinary SSBNF thickness

This module closes the quantitative bridge from the existing fixed-window
typed-yield estimate (Lemma 7.1) to the new locally-trivial typed
characteristic-sample norm theorem.

Assume every *underlying* non-start symbol has a productive untyped
word of length at most tau.  The concrete (k,l)-fixed-window reduced
refinement then has a productive typed yield no longer than
  B_{k,l}(G) = fixedWindowTypedYieldBound (k+l) |N| tau
at every active typed nonterminal.  Local triviality transports this
to the coarse h-typed canonical witness set at k=l=n=|h(Sigma+)|.

The final result bounds the encoded norm of the actual canonical witness
set by an explicit polynomial in the non-start production counts, the
number of non-start symbols, and ordinary thickness tau (for fixed h).
The transfer from arbitrary reduced CFG R to reduced SSBNF G is a
separate normalization theorem, not claimed here.
-/

namespace LeanCfgProject
namespace TCS1

universe u v z

section V115LocalThicknessBound

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {NT : Type z}

/--
The existing fixed-window Lemma 7.1 and concrete minimal canonical
choices provide *actual* short productive typed yields for the active
fixed-window refinement.
-/
theorem v115_concreteWindow_active_yield_length_bound
    [Fintype α] [Fintype NT]
    (terminalRule : NT → α → Prop)
    (binaryRule : NT → NT → NT → Prop)
    (startRule : NT → Prop)
    (epsilonStart : Prop)
    (k l τ : Nat)
    (hshort :
      ∀ A : NT,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
            ∧ z.length ≤ τ) :
    ∀ (A : NT) (ν : FixedWindowMonoid α k l),
      ConcreteTypedActive
        (fixedWindowMonoidHom (α := α) k l)
        terminalRule binaryRule startRule (A, ν) →
      ∃ z : Word α,
        TypedDerives
          (fixedWindowMonoidHom (α := α) k l)
          terminalRule binaryRule (A, ν) z
          ∧ z.length ≤
            fixedWindowTypedYieldBound
              (k + l) (Fintype.card NT) τ := by
  classical
  let F := fixedWindowMonoidHom (α := α) k l
  let C :=
    concreteTypedActive_minimalChoices
      F terminalRule binaryRule startRule epsilonStart
  have hrespect : RespectsFixedWindowSummary F k l :=
    fixedWindowMonoidHom_respects (α := α) k l
  have hminimal :
      CanonicalChoiceMinimality
        F terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          F terminalRule binaryRule startRule) C :=
    concreteTypedActive_minimalChoices_minimality
      F terminalRule binaryRule startRule epsilonStart
  have htrim :
      SuccessfulTypedTrimClosure
        F terminalRule binaryRule
        (ConcreteTypedActive
          F terminalRule binaryRule startRule) :=
    concreteTypedActive_trimClosure
      F terminalRule binaryRule startRule
  intro A ν hactive
  have hω :
      (C.omega (A, ν)).length ≤
        fixedWindowTypedYieldBound
          (k + l) (Fintype.card NT) τ :=
    (canonicalOmega_length_le_fixedWindow
      F terminalRule binaryRule startRule epsilonStart
      (ConcreteTypedActive
        F terminalRule binaryRule startRule)
      C hminimal htrim
      k l hrespect τ hshort) (A, ν) hactive
  refine ⟨C.omega (A, ν), ?_, hω⟩
  exact reducedTypedDerives_to_typedDerives
    F terminalRule binaryRule
    (ConcreteTypedActive
      F terminalRule binaryRule startRule)
    (C.omegaDerives (A, ν) hactive)

/--
Corollary 7.5 at the reduced-SSBNF grammar level.

For n=|h(Sigma+)|, all finite-algebraic and fixed-window
quantitative premises have been discharged.  The only input about
ordinary thickness is a short productive untyped yield for each
non-start symbol, precisely the tau_G premise in the manuscript.
-/
theorem v115_locallyTrivial_sampleNorm_le_ordinaryThickness
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype NT]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : NT → α → Prop)
    (binaryRule : NT → NT → NT → Prop)
    (startRule : NT → Prop)
    (epsilonStart : Prop)
    [Fintype
      (ActiveTypedSymbol
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedTerminalIndex H terminalRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype
      (ActiveTypedBinaryIndex binaryRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))]
    [Fintype (UntypedTerminalRuleIndex terminalRule)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)]
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule))
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule) C)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (τ : Nat)
    (hshort :
      ∀ A : NT,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
            ∧ z.length ≤ τ) :
    (∑ w ∈
      canonicalWitnessFinset
        H terminalRule binaryRule startRule epsilonStart
        (ConcreteTypedActive
          H terminalRule binaryRule startRule) C,
      (w.length + 1)) ≤
    typedThicknessWitnessCountEnvelope
      (Fintype.card M)
      (Fintype.card NT)
      (Fintype.card (UntypedTerminalRuleIndex terminalRule))
      (Fintype.card (UntypedBinaryRuleIndex binaryRule))
      *
      (((Fintype.card NT * Fintype.card M + 1) *
        fixedWindowTypedYieldBound
          (v115PositiveImageCard H + v115PositiveImageCard H)
          (Fintype.card NT) τ) + 1) := by
  let n := v115PositiveImageCard H
  let B :=
    fixedWindowTypedYieldBound (n + n) (Fintype.card NT) τ
  have hn : 0 < n :=
    v115_positiveImageCard_pos H
  have hB : 1 ≤ B := by
    dsimp [B]
    rw [fixedWindowTypedYieldBound_of_pos (by omega : 0 < n + n)]
    omega
  have hFineBound :
      ∀ (A : NT) (ν : FixedWindowMonoid α n n),
        ConcreteTypedActive
          (fixedWindowMonoidHom (α := α) n n)
          terminalRule binaryRule startRule (A, ν) →
        ∃ z : Word α,
          TypedDerives
            (fixedWindowMonoidHom (α := α) n n)
            terminalRule binaryRule (A, ν) z
            ∧ z.length ≤ B := by
    simpa only [B] using
      (v115_concreteWindow_active_yield_length_bound
        terminalRule binaryRule startRule epsilonStart
        n n τ hshort)
  simpa only [n, B] using
    (v115_locallyTrivial_canonicalSampleNorm_le
      H terminalRule binaryRule startRule epsilonStart
      C minimal hlocal B hB hFineBound)

end V115LocalThicknessBound
end TCS1
end LeanCfgProject
