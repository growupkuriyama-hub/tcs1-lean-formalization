import LeanCfgProject.TCS1.V115PositiveImageCardinal
import LeanCfgProject.TCS1.V115LocallyTrivialThickness

/-!
# TCS #1 v115: locally trivial typings -- learning and sample-size consequences

Now that the finite-semigroup cardinal-prefix lemma and the exact
positive-image fixed-window refinement are proved, we can discharge the
previously *conditional* transfer to canonical characteristic data.

The numerical bound in the last theorem is an exact bound on the norm
of the actual canonical witness finset, rather than merely an abstract
bound on its word lengths.  It uses the v83 witness-index counting
theorem; the premise about short productive fine-typed yields is the
separate fixed-window SSBNF yield bound.

The paper's final transfer all the way to arbitrary reduced CFG
representations (Corollary 7.5) additionally invokes the
thickness-preserving SSBNF normalization; that final glue is not
claimed in this file.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z

section V115LocalConsequences

variable {α : Type u}
variable {M : Type v} {F : Type w}
variable [Monoid M] [Fintype M]
variable [Monoid F] [Fintype F]
variable {NT : Type z}

/--
Substitutability for locally trivial positive-image typing implies
substitutability for the concrete (n,n)-fixed window at
n = |h(Sigma+)|.  This proves the nontrivial family-inclusion
direction of the KL characterization in Proposition 3.5.
-/
theorem v115_localSubstitutable_is_fixedWindowSubstitutable
    [Fintype α] [Nonempty α]
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (L : Set (Word α))
    (hsub : FixedHSubstitutable H L) :
    FixedHSubstitutable
      (fixedWindowMonoidHom
        (α := α)
        (v115PositiveImageCard H)
        (v115PositiveImageCard H))
      L := by
  intro x y hx hy heq hshared
  exact
    hsub hx hy
      ((v115_positiveImageLocallyTrivial_window_refines
        H hlocal) x y hx hy heq)
      hshared

/--
The *actual* canonical witness finset has the v83 quantitative
encoded-size bound under an arbitrary positive-kernel refinement.
-/
theorem v115_canonicalSampleNorm_le_of_refinement
    [Fintype α] [DecidableEq α] [Fintype NT]
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α F)
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
    (hrefines : V115NonemptyKernelRefines G H)
    (B : Nat)
    (hB : 1 ≤ B)
    (hFineBound :
      ∀ (A : NT) (ν : F),
        ConcreteTypedActive
          G terminalRule binaryRule startRule (A, ν) →
        ∃ v : Word α,
          TypedDerives G terminalRule binaryRule (A, ν) v
            ∧ v.length ≤ B) :
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
      (((Fintype.card NT * Fintype.card M + 1) * B) + 1) := by
  have hreach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule
        (ConcreteTypedActive
          H terminalRule binaryRule startRule) :=
    concreteTypedActive_structuralReachability
      H terminalRule binaryRule startRule epsilonStart C
  have hOmega :
      ∀ X : NT × M,
        ConcreteTypedActive
          H terminalRule binaryRule startRule X →
        (C.omega X).length ≤ B := by
    intro X hX
    exact
      v115_canonicalOmega_length_le_of_refinement
        H G terminalRule binaryRule startRule epsilonStart
        C minimal hrefines B hFineBound X hX
  exact
    canonicalWitnessFinset_sampleNorm_le_typedThickness
      H terminalRule binaryRule startRule epsilonStart
      (ConcreteTypedActive
        H terminalRule binaryRule startRule)
      C minimal hreach B hB hOmega

/--
Corollary 7.5's characteristic-sample norm estimate with the
finite-semigroup hypothesis *fully discharged*: the only remaining
premise is the short-yield bound for the concrete fixed-window
productive trim, provided by the SSBNF thickness development.
-/
theorem v115_locallyTrivial_canonicalSampleNorm_le
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
    (B : Nat)
    (hB : 1 ≤ B)
    (hFineBound :
      ∀ (A : NT)
        (ν : FixedWindowMonoid α
          (v115PositiveImageCard H)
          (v115PositiveImageCard H)),
        ConcreteTypedActive
          (fixedWindowMonoidHom
            (α := α)
            (v115PositiveImageCard H)
            (v115PositiveImageCard H))
          terminalRule binaryRule startRule (A, ν) →
        ∃ v : Word α,
          TypedDerives
            (fixedWindowMonoidHom
              (α := α)
              (v115PositiveImageCard H)
              (v115PositiveImageCard H))
            terminalRule binaryRule (A, ν) v
            ∧ v.length ≤ B) :
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
      (((Fintype.card NT * Fintype.card M + 1) * B) + 1) := by
  exact
    v115_canonicalSampleNorm_le_of_refinement
      H
      (fixedWindowMonoidHom
        (α := α)
        (v115PositiveImageCard H)
        (v115PositiveImageCard H))
      terminalRule binaryRule startRule epsilonStart
      C minimal
      (v115_positiveImageLocallyTrivial_window_refines H hlocal)
      B hB hFineBound

end V115LocalConsequences
end TCS1
end LeanCfgProject
