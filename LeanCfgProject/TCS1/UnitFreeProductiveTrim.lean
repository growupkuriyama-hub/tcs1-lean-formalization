import LeanCfgProject.TCS1.SSBNFNormalizationSemanticKernel

/-!
# TCS #1 v66: concrete productive trim after unit elimination

The normalization appendix ends by trimming useless symbols.  The existing
semantic kernel treated the final trim abstractly by an embedding of retained
states.  This file makes the productive half of that trim concrete.

A productive state is a nonterminal having some unit-free terminal derivation.
We restrict the copied unit-free terminal/binary rules to the subtype of such
states and obtain an ordinary BinaryNullableGrammar whose epsilon and unit
relations are empty.  Its explicit derivation language is exactly the ambient
UnitFreeDerives language on every retained state.

Consequently every retained state is genuinely productive in the restricted
grammar, and any uniform shortest-yield bound transfers without loss.
Reachability from a designated start symbol is intentionally kept as the next,
separate trim layer.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section UnitFreeProductiveTrim

variable {N : Type u}
variable {α : Type v}

/-- States having at least one terminal derivation after unit elimination. -/
abbrev ProductiveUnitFreeState
    (G : BinaryNullableGrammar N α) :=
  {A : N // ∃ w, UnitFreeDerives G A w}

/--
Grammar obtained by retaining only productive states and the terminal/binary
rules of the copied unit-free presentation.
-/
def productiveUnitFreeGrammar
    (G : BinaryNullableGrammar N α) :
    BinaryNullableGrammar
      (ProductiveUnitFreeState G) α where
  terminalRule A a :=
    UnitFreeTerminalRule G A.1 a
  binaryRule A B C :=
    UnitFreeBinaryRule G A.1 B.1 C.1
  epsilonRule _ :=
    False
  unitRule _ _ :=
    False

/-- Forgetting productivity annotations maps restricted derivations back. -/
theorem productiveTrimDerives_to_unitFree
    (G : BinaryNullableGrammar N α)
    {A : ProductiveUnitFreeState G}
    {w : List α}
    (d : BinaryNullableDerives
      (productiveUnitFreeGrammar G) A w) :
    UnitFreeDerives G A.1 w := by
  induction d with
  | terminal h =>
      exact UnitFreeDerives.terminal h
  | epsilon h =>
      exact False.elim h
  | unit h _ _ =>
      exact False.elim h
  | binary h _ _ ihB ihC =>
      exact UnitFreeDerives.binary h ihB ihC

/--
Every ambient unit-free derivation rooted at a productive state lifts to the
productive restricted grammar.
-/
theorem unitFreeDerives_to_productiveTrim
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    (hprod : ∃ u, UnitFreeDerives G A u)
    (d : UnitFreeDerives G A w) :
    BinaryNullableDerives
      (productiveUnitFreeGrammar G)
      (⟨A, hprod⟩ : ProductiveUnitFreeState G)
      w := by
  induction d with
  | @terminal A a h =>
      exact BinaryNullableDerives.terminal h
  | @binary A B C wB wC h dB dC ihB ihC =>
      let B' : ProductiveUnitFreeState G :=
        ⟨B, ⟨wB, dB⟩⟩
      let C' : ProductiveUnitFreeState G :=
        ⟨C, ⟨wC, dC⟩⟩
      have h' :
          (productiveUnitFreeGrammar G).binaryRule
            (⟨A, hprod⟩ : ProductiveUnitFreeState G)
            B' C' := by
        exact h
      exact
        BinaryNullableDerives.binary h'
          (ihB ⟨wB, dB⟩)
          (ihC ⟨wC, dC⟩)

/-- Exact language preservation on every retained productive state. -/
theorem productiveTrimDerives_iff_unitFree
    (G : BinaryNullableGrammar N α)
    (A : ProductiveUnitFreeState G)
    (w : List α) :
    BinaryNullableDerives
        (productiveUnitFreeGrammar G) A w
      ↔
    UnitFreeDerives G A.1 w := by
  constructor
  · exact productiveTrimDerives_to_unitFree G
  · intro d
    exact
      unitFreeDerives_to_productiveTrim
        G A.2 d

/-- No epsilon rule survives the productive unit-free trim. -/
theorem productiveUnitFreeGrammar_no_epsilon
    (G : BinaryNullableGrammar N α)
    (A : ProductiveUnitFreeState G) :
    ¬ (productiveUnitFreeGrammar G).epsilonRule A := by
  simp [productiveUnitFreeGrammar]

/-- No unit rule survives the productive unit-free trim. -/
theorem productiveUnitFreeGrammar_no_unit
    (G : BinaryNullableGrammar N α)
    (A B : ProductiveUnitFreeState G) :
    ¬ (productiveUnitFreeGrammar G).unitRule A B := by
  simp [productiveUnitFreeGrammar]

/-- Every state of the restricted grammar has a terminal derivation there. -/
theorem productiveUnitFreeGrammar_all_productive
    (G : BinaryNullableGrammar N α) :
    ∀ A : ProductiveUnitFreeState G,
      ∃ w,
        BinaryNullableDerives
          (productiveUnitFreeGrammar G) A w := by
  intro A
  obtain ⟨w, hw⟩ := A.2
  exact
    ⟨w,
      (productiveTrimDerives_iff_unitFree G A w).2 hw⟩

/-- Every retained derivation is nonempty. -/
theorem productiveTrimDerives_nonempty
    (G : BinaryNullableGrammar N α)
    {A : ProductiveUnitFreeState G}
    {w : List α}
    (d : BinaryNullableDerives
      (productiveUnitFreeGrammar G) A w) :
    w ≠ [] := by
  exact
    unitFreeDerives_nonempty G
      (productiveTrimDerives_to_unitFree G d)

/-- A uniform shortest-yield bound transfers unchanged to productive trim. -/
theorem yieldBound_productiveTrim
    (G : BinaryNullableGrammar N α)
    (b : Nat)
    (hbound :
      YieldBound
        (fun A => {w | UnitFreeDerives G A w})
        b) :
    YieldBound
      (fun A : ProductiveUnitFreeState G =>
        {w | BinaryNullableDerives
          (productiveUnitFreeGrammar G) A w})
      b := by
  intro A
  obtain ⟨w, hw, hlen⟩ := hbound A.1
  exact
    ⟨w,
      (productiveTrimDerives_iff_unitFree
        G A w).2 hw,
      hlen⟩

/--
The productive subtype is exactly a concrete realization of the abstract
"all retained states have a nonempty yield" premise used by the normalization
semantic kernel.
-/
theorem productiveTrim_allHaveNonempty
    (G : BinaryNullableGrammar N α) :
    AllHaveNonemptyYield
      (fun A : ProductiveUnitFreeState G =>
        {w | BinaryNullableDerives
          (productiveUnitFreeGrammar G) A w}) := by
  intro A
  obtain ⟨w, hw⟩ :=
    productiveUnitFreeGrammar_all_productive G A
  exact
    ⟨w, hw,
      productiveTrimDerives_nonempty G hw⟩

end UnitFreeProductiveTrim

end TCS1
end LeanCfgProject
