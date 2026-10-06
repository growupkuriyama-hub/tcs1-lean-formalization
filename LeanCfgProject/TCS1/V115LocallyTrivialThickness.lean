import LeanCfgProject.TCS1.V115LocallyTrivialForwardReduction
import LeanCfgProject.TCS1.ConcreteTypedTrimming

/-!
# TCS #1 v115: productive/reachable typed-refinement transfer

Corollary 7.5 compares ordinary thickness with typed thickness for a
locally-trivial positive-image typing, via a fixed-window refinement.

The proof needs a semantic transfer that had not been isolated in the
archived v88 modules: every *successful derivation* rooted at an active
coarse typed symbol can be reannotated at a finer typing and its refined
root remains active after productive/reachable trimming.  This is true
for any two finite-monoid typings, not just locally trivial ones.

Consequently, when the finer typing refines the coarse kernel on
nonempty words, any common bound on productive yields of fine active
symbols also bounds productive yields of coarse active symbols.

These results are proof bridges, not a claim that the full polynomial
characteristic-data Corollary 7.5 has yet been discharged.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z

section V115LocallyTrivialThickness

variable {α : Type u}
variable {M : Type v} {F : Type w}
variable [Monoid M] [Fintype M]
variable [Monoid F] [Fintype F]
variable {NT : Type z}

/--
A successful derivation at an active H-typed nonterminal survives
productive/reachable trimming after retyping the *same yield* by G.

This important compatibility does not require any kernel inclusion:
only the successful derivation and its reaching context are used.
-/
theorem v115_active_retyping
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α F)
    (terminalRule : NT → α → Prop)
    (binaryRule : NT → NT → NT → Prop)
    (startRule : NT → Prop)
    {X : NT × M}
    (hactive :
      ConcreteTypedActive
        H terminalRule binaryRule startRule X)
    {w : Word α}
    (d :
      TypedDerives H terminalRule binaryRule X w) :
    ConcreteTypedActive
      G terminalRule binaryRule startRule
      (X.1, G.h w) := by
  induction hactive generalizing w with
  | @start A μ hstart hprod =>
      have dFine :
          TypedDerives G terminalRule binaryRule
            (A, G.h w) w :=
        untypedDerives_lift G terminalRule binaryRule
          (typedDerives_erase H terminalRule binaryRule d)
      exact ProductiveTypedReachable.start
        hstart ⟨w, dFine⟩
  | @left A B C μ ν hparent hbin hprodB hprodC ih =>
      rcases hprodC with ⟨wC, dC⟩
      have dParent :
          TypedDerives H terminalRule binaryRule
            (A, μ * ν) (w ++ wC) :=
        TypedDerives.binary hbin d dC
      have hParentFine :
          ConcreteTypedActive
            G terminalRule binaryRule startRule
            (A, G.h (w ++ wC)) :=
        ih dParent
      rw [G.map_append w wC] at hParentFine
      have dBFine :
          TypedDerives G terminalRule binaryRule
            (B, G.h w) w :=
        untypedDerives_lift G terminalRule binaryRule
          (typedDerives_erase H terminalRule binaryRule d)
      have dCFine :
          TypedDerives G terminalRule binaryRule
            (C, G.h wC) wC :=
        untypedDerives_lift G terminalRule binaryRule
          (typedDerives_erase H terminalRule binaryRule dC)
      exact ProductiveTypedReachable.left
        hParentFine hbin ⟨w, dBFine⟩ ⟨wC, dCFine⟩
  | @right A B C μ ν hparent hbin hprodB hprodC ih =>
      rcases hprodB with ⟨wB, dB⟩
      have dParent :
          TypedDerives H terminalRule binaryRule
            (A, μ * ν) (wB ++ w) :=
        TypedDerives.binary hbin dB d
      have hParentFine :
          ConcreteTypedActive
            G terminalRule binaryRule startRule
            (A, G.h (wB ++ w)) :=
        ih dParent
      rw [G.map_append wB w] at hParentFine
      have dBFine :
          TypedDerives G terminalRule binaryRule
            (B, G.h wB) wB :=
        untypedDerives_lift G terminalRule binaryRule
          (typedDerives_erase H terminalRule binaryRule dB)
      have dCFine :
          TypedDerives G terminalRule binaryRule
            (C, G.h w) w :=
        untypedDerives_lift G terminalRule binaryRule
          (typedDerives_erase H terminalRule binaryRule d)
      exact ProductiveTypedReachable.right
        hParentFine hbin ⟨wB, dBFine⟩ ⟨w, dCFine⟩

/--
Positive-kernel refinement transports any uniform fine typed-yield bound
to every active symbol of the coarse typed grammar.

The coarse symbol's chosen witness first gets an active fine annotation.
Its bounded fine replacement has the same fine type and, since yields
are nonempty, must also have the same coarse type.
-/
theorem v115_active_yield_bound_of_refinement
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α F)
    (terminalRule : NT → α → Prop)
    (binaryRule : NT → NT → NT → Prop)
    (startRule : NT → Prop)
    (hrefines : V115NonemptyKernelRefines G H)
    (B : Nat)
    (hFineBound :
      ∀ (A : NT) (ν : F),
        ConcreteTypedActive
          G terminalRule binaryRule startRule (A, ν) →
        ∃ v : Word α,
          TypedDerives G terminalRule binaryRule (A, ν) v
            ∧ v.length ≤ B)
    {A : NT} {μ : M}
    (hactive :
      ConcreteTypedActive
        H terminalRule binaryRule startRule (A, μ)) :
    ∃ v : Word α,
      TypedDerives H terminalRule binaryRule (A, μ) v
        ∧ v.length ≤ B := by
  obtain ⟨w, dH⟩ :=
    concreteTypedActive_productive
      H terminalRule binaryRule startRule hactive
  have hActiveFine :
      ConcreteTypedActive
        G terminalRule binaryRule startRule
        (A, G.h w) :=
    v115_active_retyping
      H G terminalRule binaryRule startRule hactive dH
  obtain ⟨v, dG, hvlen⟩ :=
    hFineBound A (G.h w) hActiveFine
  have hwne : w ≠ [] := by
    intro hw
    have hp :=
      typedDerives_length_pos
        H terminalRule binaryRule dH
    simp [hw] at hp
  have hvne : v ≠ [] := by
    intro hv
    have hp :=
      typedDerives_length_pos
        G terminalRule binaryRule dG
    simp [hv] at hp
  have hfine : G.h v = G.h w :=
    typedDerives_yield_type
      G terminalRule binaryRule dG
  have hcoarse : H.h v = μ := by
    calc
      H.h v = H.h w :=
        hrefines v w hvne hwne hfine
      _ = μ :=
        typedDerives_yield_type
          H terminalRule binaryRule dH
  have dHreplace :
      TypedDerives H terminalRule binaryRule
        (A, H.h v) v :=
    untypedDerives_lift H terminalRule binaryRule
      (typedDerives_erase G terminalRule binaryRule dG)
  exact ⟨v, by simpa only [hcoarse] using dHreplace, hvlen⟩

/--
Corollary 7.5's typed-yield transfer, conditional on the last
length-n idempotence lemma in Proposition 3.5.

The previously proved forward reduction supplies the necessary
fixed-window kernel inclusion.
-/
theorem v115_locallyTrivial_active_yield_bound
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : NT → α → Prop)
    (binaryRule : NT → NT → NT → Prop)
    (startRule : NT → Prop)
    (n : Nat)
    (hn : 0 < n)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (hidempotent :
      ∀ p : Word α,
        p.length = n →
        H.h p * H.h p = H.h p)
    (B : Nat)
    (hFineBound :
      ∀ (A : NT) (ν : FixedWindowMonoid α n n),
        ConcreteTypedActive
          (fixedWindowMonoidHom (α := α) n n)
          terminalRule binaryRule startRule (A, ν) →
        ∃ v : Word α,
          TypedDerives
            (fixedWindowMonoidHom (α := α) n n)
            terminalRule binaryRule (A, ν) v
            ∧ v.length ≤ B)
    {A : NT} {μ : M}
    (hactive :
      ConcreteTypedActive
        H terminalRule binaryRule startRule (A, μ)) :
    ∃ v : Word α,
      TypedDerives H terminalRule binaryRule (A, μ) v
        ∧ v.length ≤ B := by
  exact
    v115_active_yield_bound_of_refinement
      H (fixedWindowMonoidHom (α := α) n n)
      terminalRule binaryRule startRule
      (v115_windowRefinement_of_lengthIdempotence
        H n hn hlocal hidempotent)
      B hFineBound hactive

end V115LocallyTrivialThickness

end TCS1
end LeanCfgProject
