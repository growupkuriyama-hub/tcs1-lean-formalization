import LeanCfgProject.TCS1.FiniteSupportSpineBound

/-!
# TCS #1 v66: restriction of a binary grammar to finite support

The front-end semantic grammar may use an infinite ambient state type even
though a concrete finite input creates only finitely many states.  This module
turns any finite rule-closed support into an actual finite-state
BinaryNullableGrammar by taking the subtype of supported states.

Derivations of the restricted grammar are exactly derivations of the ambient
grammar whose root lies in the support.  Thus all finite-type theorems already
proved for epsilon elimination, unit elimination, and Proposition 7.4 can be
applied to the supported grammar without changing its terminal languages.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryGrammarFiniteRestriction

variable {N : Type u}
variable {α : Type v}

/-- The finite subtype represented by a support finset. -/
abbrev SupportedState
    [DecidableEq N]
    (support : Finset N) :=
  {A : N // A ∈ support}

/-- Restrict every rule of a binary grammar to supported state indices. -/
def restrictBinaryGrammar
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N) :
    BinaryNullableGrammar (SupportedState support) α where
  terminalRule A a :=
    G.terminalRule A.1 a
  binaryRule A B C :=
    G.binaryRule A.1 B.1 C.1
  epsilonRule A :=
    G.epsilonRule A.1
  unitRule A B :=
    G.unitRule A.1 B.1

/-- Forgetting support annotations maps every restricted derivation back. -/
theorem restrictedDerives_to_ambient
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N)
    {A : SupportedState support}
    {w : List α}
    (d : BinaryNullableDerives
      (restrictBinaryGrammar G support) A w) :
    BinaryNullableDerives G A.1 w := by
  induction d with
  | terminal h =>
      exact BinaryNullableDerives.terminal h
  | epsilon h =>
      exact BinaryNullableDerives.epsilon h
  | unit h d ih =>
      exact BinaryNullableDerives.unit h ih
  | binary h dB dC ihB ihC =>
      exact BinaryNullableDerives.binary h ihB ihC

/--
If the support is rule-closed, every ambient derivation rooted in the support
lifts uniquely enough to a restricted derivation.
-/
theorem ambientDerives_to_restricted
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N)
    (hclosed : BinaryGrammarSupportedOn G support)
    {A : N}
    {w : List α}
    (hA : A ∈ support)
    (d : BinaryNullableDerives G A w) :
    BinaryNullableDerives
      (restrictBinaryGrammar G support)
      (⟨A, hA⟩ : SupportedState support)
      w := by
  induction d with
  | @terminal A a h =>
      exact BinaryNullableDerives.terminal h
  | @epsilon A h =>
      exact BinaryNullableDerives.epsilon h
  | @unit A B w h d ih =>
      have hB : B ∈ support :=
        hclosed.unitChild hA h
      let A' : SupportedState support := ⟨A, hA⟩
      let B' : SupportedState support := ⟨B, hB⟩
      have h' :
          (restrictBinaryGrammar G support).unitRule A' B' := by
        exact h
      exact
        BinaryNullableDerives.unit h'
          (ih hB)
  | @binary A B C wB wC h dB dC ihB ihC =>
      have hBC :=
        hclosed.binaryChildren hA h
      let A' : SupportedState support := ⟨A, hA⟩
      let B' : SupportedState support := ⟨B, hBC.1⟩
      let C' : SupportedState support := ⟨C, hBC.2⟩
      have h' :
          (restrictBinaryGrammar G support).binaryRule A' B' C' := by
        exact h
      exact
        BinaryNullableDerives.binary h'
          (ihB hBC.1)
          (ihC hBC.2)

/-- Exact language equivalence between ambient and restricted derivations. -/
theorem restrictedDerives_iff_ambient
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N)
    (hclosed : BinaryGrammarSupportedOn G support)
    (A : SupportedState support)
    (w : List α) :
    BinaryNullableDerives
        (restrictBinaryGrammar G support) A w
      ↔
    BinaryNullableDerives G A.1 w := by
  constructor
  · exact restrictedDerives_to_ambient G support
  · intro d
    exact ambientDerives_to_restricted
      G support hclosed A.2 d

/-- The supported subtype has cardinality exactly the support finset. -/
@[simp] theorem supportedState_card
    [DecidableEq N]
    (support : Finset N) :
    Fintype.card (SupportedState support) =
      support.card := by
  simpa [SupportedState] using
    (Fintype.card_coe support)

/--
A local yield bound on the support becomes an ordinary global yield bound on
the finite restricted grammar.
-/
theorem yieldBound_restrictBinaryGrammar
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N)
    (hclosed : BinaryGrammarSupportedOn G support)
    (b : Nat)
    (hbound :
      YieldBoundOn
        (fun A => {w | BinaryNullableDerives G A w})
        support b) :
    YieldBound
      (fun A =>
        {w | BinaryNullableDerives
          (restrictBinaryGrammar G support) A w})
      b := by
  intro A
  obtain ⟨w, hw, hlen⟩ :=
    hbound A.1 A.2
  exact
    ⟨w,
      ambientDerives_to_restricted
        G support hclosed A.2 hw,
      hlen⟩

/--
Likewise, a nonempty-yield bound on the support transfers to the finite
restricted grammar.
-/
theorem nonemptyYieldBound_restrictBinaryGrammar
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N)
    (hclosed : BinaryGrammarSupportedOn G support)
    (b : Nat)
    (hbound :
      NonemptyYieldBoundOn
        (fun A => {w | BinaryNullableDerives G A w})
        support b) :
    NonemptyYieldBound
      (fun A =>
        {w | BinaryNullableDerives
          (restrictBinaryGrammar G support) A w})
      b := by
  intro A hExists
  have hExistsAmbient :
      ∃ w,
        BinaryNullableDerives G A.1 w ∧
        w ≠ [] := by
    rcases hExists with ⟨w, hw, hne⟩
    exact
      ⟨w,
        restrictedDerives_to_ambient
          G support hw,
        hne⟩
  obtain ⟨w, hw, hne, hlen⟩ :=
    hbound A.1 A.2 hExistsAmbient
  exact
    ⟨w,
      ambientDerives_to_restricted
        G support hclosed A.2 hw,
      hne,
      hlen⟩

/--
The finite-support shortest-nonempty bound can therefore be stated directly as
a standard NonemptyYieldBound on a genuinely finite nonterminal type.
-/
theorem restricted_nonemptyYieldBound_of_yieldBoundOn
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N)
    (τB : Nat)
    (hclosed : BinaryGrammarSupportedOn G support)
    (hshort :
      YieldBoundOn
        (fun A => {w | BinaryNullableDerives G A w})
        support τB) :
    NonemptyYieldBound
      (fun A =>
        {w | BinaryNullableDerives
          (restrictBinaryGrammar G support) A w})
      (1 + support.card * τB) := by
  have hlocal :
      NonemptyYieldBoundOn
        (fun A => {w | BinaryNullableDerives G A w})
        support
        (1 + support.card * τB) :=
    nonemptyYieldBoundOn_of_yieldBoundOn
      G support τB hclosed hshort
  exact
    nonemptyYieldBound_restrictBinaryGrammar
      G support hclosed
      (1 + support.card * τB)
      hlocal

end BinaryGrammarFiniteRestriction

end TCS1
end LeanCfgProject
