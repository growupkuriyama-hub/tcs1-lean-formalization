import LeanCfgProject.TCS1.ClarkCongruentialKernel
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage
import LeanCfgProject.TCS1.ReducedTypedRuleBridge
import LeanCfgProject.TCS1.BinaryEpsilonElimination

/-!
# TCS #1 v78: finite-initial-set packaging for Clark congruentiality

Section 9 removes the separated start symbol from the reduced yield-typed
grammar and uses its surviving typed start children as a finite initial set.
If epsilon belongs to the target, one fresh symbol generating only epsilon is
added to that initial set.

This file formalizes exactly that packaging step inside the repository's
binary CFG semantics.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section ClarkCongruentialPackaging

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Language generated from a finite initial set of nonterminals. -/
def InitialSetLanguage
    {X : Type*}
    (G : BinaryNullableGrammar X α)
    (I : Set X) :
    Set (Word α) :=
  { w | ∃ A : X, A ∈ I ∧ BinaryNullableDerives G A w }

/--
Clark's congruential condition in pairwise form: every nonterminal language
is contained in one syntactic-congruence class of the initial-set language.
-/
def ClarkCongruentialInitialSet
    {X : Type*}
    (G : BinaryNullableGrammar X α)
    (I : Set X) : Prop :=
  ∀ A : X, ∀ x y : Word α,
    BinaryNullableDerives G A x →
    BinaryNullableDerives G A y →
    Distribution (InitialSetLanguage G I) x =
      Distribution (InitialSetLanguage G I) y

/-- Surviving typed nonterminals of the concrete productive/reachable trim. -/
abbrev ClarkActiveSymbol
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :=
  ActiveTypedSymbol
    (ConcreteTypedActive H terminalRule binaryRule startRule)

/--
Nonterminals after removing the separated start.  'some X' is an old reduced
typed nonterminal; 'none' is the optional fresh epsilon-only symbol.
-/
abbrev ClarkPackagedState
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop) :=
  Option (ClarkActiveSymbol H terminalRule binaryRule startRule)

/-- The grammar obtained after deleting the separated start symbol. -/
def clarkPackagedGrammar
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    BinaryNullableGrammar
      (ClarkPackagedState H terminalRule binaryRule startRule) α where
  terminalRule X a :=
    match X with
    | none => False
    | some Y =>
        ActiveTypedTerminalRule
          H terminalRule
          (ConcreteTypedActive
            H terminalRule binaryRule startRule)
          Y a
  binaryRule X Y Z :=
    match X, Y, Z with
    | some A, some B, some C =>
        ActiveTypedBinaryRule
          binaryRule
          (ConcreteTypedActive
            H terminalRule binaryRule startRule)
          A B C
    | _, _, _ => False
  epsilonRule X :=
    match X with
    | none => epsilonStart
    | some _ => False
  unitRule _ _ := False

/--
Initial set after start removal: all surviving typed children of start rules,
plus the fresh epsilon symbol exactly when epsilon is generated.
-/
def clarkPackagedInitial
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    Set (ClarkPackagedState H terminalRule binaryRule startRule) :=
  { X |
      match X with
      | none => epsilonStart
      | some Y => startRule Y.1.1 }

/-- Active-typed derivations embed into the packaged grammar under 'some'. -/
theorem activeUntypedDerives_to_clarkPackaged
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    {X : ClarkActiveSymbol H terminalRule binaryRule startRule}
    {w : Word α}
    (d :
      UntypedDerives
        (ActiveTypedTerminalRule
          H terminalRule
          (ConcreteTypedActive
            H terminalRule binaryRule startRule))
        (ActiveTypedBinaryRule
          binaryRule
          (ConcreteTypedActive
            H terminalRule binaryRule startRule))
        X w) :
    BinaryNullableDerives
      (clarkPackagedGrammar
        H terminalRule binaryRule startRule epsilonStart)
      (some X) w := by
  induction d with
  | terminal hterm =>
      exact BinaryNullableDerives.terminal hterm
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      have hpack :
          (clarkPackagedGrammar
            H terminalRule binaryRule startRule epsilonStart).binaryRule
            (some A) (some B) (some C) := by
        simpa [clarkPackagedGrammar] using hbin
      exact BinaryNullableDerives.binary hpack ihB ihC

/--
Shape of every packaged derivation.  The fresh symbol derives only epsilon;
an old symbol has exactly its active-typed derivations.
-/
theorem clarkPackaged_derivation_shape
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    {X : ClarkPackagedState H terminalRule binaryRule startRule}
    {w : Word α}
    (d :
      BinaryNullableDerives
        (clarkPackagedGrammar
          H terminalRule binaryRule startRule epsilonStart)
        X w) :
    match X with
    | none => w = [] ∧ epsilonStart
    | some Y =>
        UntypedDerives
          (ActiveTypedTerminalRule
            H terminalRule
            (ConcreteTypedActive
              H terminalRule binaryRule startRule))
          (ActiveTypedBinaryRule
            binaryRule
            (ConcreteTypedActive
              H terminalRule binaryRule startRule))
          Y w := by
  induction d with
  | @terminal X a h =>
      cases X with
      | none =>
          exact False.elim h
      | some Y =>
          exact UntypedDerives.terminal h
  | @epsilon X h =>
      cases X with
      | none =>
          exact ⟨rfl, h⟩
      | some Y =>
          exact False.elim h
  | @unit X Y word h d ih =>
      exact False.elim h
  | @binary X Y Z wY wZ h dY dZ ihY ihZ =>
      cases X with
      | none =>
          exact False.elim h
      | some A =>
          cases Y with
          | none =>
              exact False.elim h
          | some B =>
              cases Z with
              | none =>
                  exact False.elim h
              | some C =>
                  exact UntypedDerives.binary h ihY ihZ

/--
The finite-initial-set language of the packaged grammar is exactly the reduced
typed start language.
-/
theorem clarkPackaged_language_eq_reducedTyped
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    InitialSetLanguage
        (clarkPackagedGrammar
          H terminalRule binaryRule startRule epsilonStart)
        (clarkPackagedInitial
          H terminalRule binaryRule startRule epsilonStart)
      =
    ReducedTypedLanguage
      H terminalRule binaryRule startRule epsilonStart
      (ConcreteTypedActive
        H terminalRule binaryRule startRule) := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨X, hinit, d⟩
    cases X with
    | none =>
        have hshape :=
          clarkPackaged_derivation_shape
            H terminalRule binaryRule startRule epsilonStart d
        rcases hshape with ⟨rfl, heps⟩
        exact ReducedTypedStartDerives.epsilon heps
    | some Y =>
        have hstart : startRule Y.1.1 := hinit
        have dActive :=
          clarkPackaged_derivation_shape
            H terminalRule binaryRule startRule epsilonStart d
        have dReduced :=
          activeUntypedDerives_to_reducedTypedDerives
            H terminalRule binaryRule
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)
            dActive
        exact
          ReducedTypedStartDerives.nonempty
            hstart Y.2 dReduced
  · intro hw
    cases hw with
    | @nonempty A μ word hstart hactive d =>
        let Y :
            ClarkActiveSymbol
              H terminalRule binaryRule startRule :=
          ⟨(A, μ), hactive⟩
        have dActive :=
          reducedTypedDerives_to_activeUntypedDerives
            H terminalRule binaryRule
            (ConcreteTypedActive
              H terminalRule binaryRule startRule)
            d
        refine ⟨some Y, ?_, ?_⟩
        · exact hstart
        · exact
            activeUntypedDerives_to_clarkPackaged
              H terminalRule binaryRule startRule epsilonStart
              dActive
    | epsilon heps =>
        refine ⟨none, heps, ?_⟩
        exact BinaryNullableDerives.epsilon heps

/-- The packaged initial set is finite whenever the source nonterminal set is finite. -/
theorem clarkPackagedInitial_finite
    [Finite N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    (clarkPackagedInitial
      H terminalRule binaryRule startRule epsilonStart).Finite := by
  exact Set.toFinite _

/--
Every nonterminal of the packaged grammar generates a single syntactic
congruence class of its initial-set language.
-/
theorem clarkPackaged_congruential
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    ClarkCongruentialInitialSet
      (clarkPackagedGrammar
        H terminalRule binaryRule startRule epsilonStart)
      (clarkPackagedInitial
        H terminalRule binaryRule startRule epsilonStart) := by
  let Active :=
    ConcreteTypedActive
      H terminalRule binaryRule startRule
  let Lred :=
    ReducedTypedLanguage
      H terminalRule binaryRule startRule epsilonStart Active
  have hsubRed :
      FixedHSubstitutable H Lred := by
    exact
      concreteTypedActive_fixedHSubstitutable
        H terminalRule binaryRule startRule epsilonStart hsub
  have hlang :
      InitialSetLanguage
          (clarkPackagedGrammar
            H terminalRule binaryRule startRule epsilonStart)
          (clarkPackagedInitial
            H terminalRule binaryRule startRule epsilonStart)
        =
      Lred := by
    exact
      clarkPackaged_language_eq_reducedTyped
        H terminalRule binaryRule startRule epsilonStart

  intro X x y dx dy
  cases X with
  | none =>
      have hx :=
        clarkPackaged_derivation_shape
          H terminalRule binaryRule startRule epsilonStart dx
      have hy :=
        clarkPackaged_derivation_shape
          H terminalRule binaryRule startRule epsilonStart dy
      rcases hx with ⟨rfl, _⟩
      rcases hy with ⟨rfl, _⟩
      rfl
  | some Y =>
      have dxActive :=
        clarkPackaged_derivation_shape
          H terminalRule binaryRule startRule epsilonStart dx
      have dyActive :=
        clarkPackaged_derivation_shape
          H terminalRule binaryRule startRule epsilonStart dy
      have dxReduced :
          ReducedTypedDerives
            H terminalRule binaryRule Active Y.1 x :=
        activeUntypedDerives_to_reducedTypedDerives
          H terminalRule binaryRule Active dxActive
      have dyReduced :
          ReducedTypedDerives
            H terminalRule binaryRule Active Y.1 y :=
        activeUntypedDerives_to_reducedTypedDerives
          H terminalRule binaryRule Active dyActive
      obtain ⟨ctx⟩ :=
        concreteTypedActive_reachingContext_exists
          H terminalRule binaryRule startRule epsilonStart Y.2
      have hxL : ctx.left ++ x ++ ctx.right ∈ Lred :=
        ctx.plug dxReduced
      have hyL : ctx.left ++ y ++ ctx.right ∈ Lred :=
        ctx.plug dyReduced
      have hxne : x ≠ [] :=
        List.ne_nil_of_length_pos
          (untypedDerives_length_pos
            (ActiveTypedTerminalRule
              H terminalRule Active)
            (ActiveTypedBinaryRule
              binaryRule Active)
            dxActive)
      have hyne : y ≠ [] :=
        List.ne_nil_of_length_pos
          (untypedDerives_length_pos
            (ActiveTypedTerminalRule
              H terminalRule Active)
            (ActiveTypedBinaryRule
              binaryRule Active)
            dyActive)
      have htype : H.h x = H.h y := by
        calc
          H.h x = Y.1.2 :=
            reducedTypedDerives_yield_type
              H terminalRule binaryRule Active dxReduced
          _ = H.h y :=
            (reducedTypedDerives_yield_type
              H terminalRule binaryRule Active dyReduced).symm
      have hdist :
          Distribution Lred x =
            Distribution Lred y :=
        hsubRed hxne hyne htype
          ⟨ctx.left, ctx.right, hxL, hyL⟩
      rw [hlang]
      exact hdist

/--
Paper-facing finite-initial-set form of the fixed-h-to-congruential inclusion
for a finite start-separated SSBNF presentation.
-/
theorem fixedH_has_Clark_congruential_packaging
    [Finite N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    (clarkPackagedInitial
        H terminalRule binaryRule startRule epsilonStart).Finite
      ∧
    InitialSetLanguage
        (clarkPackagedGrammar
          H terminalRule binaryRule startRule epsilonStart)
        (clarkPackagedInitial
          H terminalRule binaryRule startRule epsilonStart)
      =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart
      ∧
    ClarkCongruentialInitialSet
      (clarkPackagedGrammar
        H terminalRule binaryRule startRule epsilonStart)
      (clarkPackagedInitial
        H terminalRule binaryRule startRule epsilonStart) := by
  refine ⟨clarkPackagedInitial_finite
      H terminalRule binaryRule startRule epsilonStart, ?_, ?_⟩
  · calc
      InitialSetLanguage
          (clarkPackagedGrammar
            H terminalRule binaryRule startRule epsilonStart)
          (clarkPackagedInitial
            H terminalRule binaryRule startRule epsilonStart)
        =
      ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart
          (ConcreteTypedActive
            H terminalRule binaryRule startRule) :=
        clarkPackaged_language_eq_reducedTyped
          H terminalRule binaryRule startRule epsilonStart
      _ =
      UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart :=
        concreteTypedActive_language_eq_untyped
          H terminalRule binaryRule startRule epsilonStart
  · exact
      clarkPackaged_congruential
        H terminalRule binaryRule startRule epsilonStart hsub

end ClarkCongruentialPackaging

end TCS1
end LeanCfgProject
