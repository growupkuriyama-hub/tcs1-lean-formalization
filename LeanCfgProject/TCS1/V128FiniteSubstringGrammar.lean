import LeanCfgProject.TCS1.V128SubstringCFGPresentation
import LeanCfgProject.TCS1.ReconstructionFactorSlotState

/-!
# TCS #1 v128: finite observed-factor grammar

The v116 batch grammar has exactly one active nonterminal per observed
nonempty factor of a finite sample K. We represent these states by
\`ObservedSubstringNonterminal K\`, prove that the type is finite via
an injection into the existing computable two-cut occurrence slot space,
and give a binary/terminal/unit CFG on this finite state type.

The non-start derivations and the start language are extensionally equal
to the already Lean-checked v116 substring semantics, including epsilon.

The state count is bounded by the quadratic two-cut slot count.
This theorem does not yet certify the literal encoded grammar size
or the sharper O(n^4) rule enumeration for the v116 constructor.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FiniteSubstring

variable {α : Type u} {M : Type v}
variable [DecidableEq α] [Monoid M] [Fintype M]

/-- A unique state per distinct nonempty factor observed in sample K. -/
abbrev ObservedSubstringNonterminal (K : Finset (Word α)) :=
  {x : Word α // ∃ p q : Word α, Observed K x p q}

/-- Observed substring states have a nonempty factor. -/
theorem observedSubstring_ne_nil
    (K : Finset (Word α))
    (A : ObservedSubstringNonterminal K) : A.1 ≠ [] := by
  rcases A.2 with ⟨p, q, hobs⟩
  exact hobs.1

/-- Choose an observed occurrence slot representing an observed substring. -/
noncomputable def observedSubstringToSlot
    (K : Finset (Word α))
    (A : ObservedSubstringNonterminal K) :
    ReconstructionFactorSlot K := by
  classical
  let p := Classical.choose A.2
  let hp := Classical.choose_spec A.2
  let q := Classical.choose hp
  have hobs : Observed K A.1 p q := Classical.choose_spec hp
  exact observedReconstructionFactorSlot K hobs

/-- The chosen occurrence slot decodes to the correct factor. -/
theorem observedSubstringToSlot_factor
    (K : Finset (Word α))
    (A : ObservedSubstringNonterminal K) :
    (reconstructionFactorSlotNonterminal
      (observedSubstringToSlot K A)).factor = A.1 := by
  simp [observedSubstringToSlot,
    reconstructionFactorSlotNonterminal_observed]

/-- Distinct substring states have distinct selected occurrence slots. -/
theorem observedSubstringToSlot_injective
    (K : Finset (Word α)) :
    Function.Injective (observedSubstringToSlot K) := by
  intro A B h
  apply Subtype.ext
  calc
    A.1 = (reconstructionFactorSlotNonterminal
      (observedSubstringToSlot K A)).factor :=
        (observedSubstringToSlot_factor K A).symm
    _ = (reconstructionFactorSlotNonterminal
      (observedSubstringToSlot K B)).factor := by rw [h]
    _ = B.1 := observedSubstringToSlot_factor K B

/-- A genuine finite type of observed-factor states, with no duplicates. -/
noncomputable def observedSubstringFintype
    (K : Finset (Word α)) :
    Fintype (ObservedSubstringNonterminal K) :=
  Fintype.ofInjective
    (observedSubstringToSlot K)
    (observedSubstringToSlot_injective K)

/-- Number of distinct observed factors is quadratically bounded. -/
theorem observedSubstring_card_le_sq
    (K : Finset (Word α)) :
    @Fintype.card (ObservedSubstringNonterminal K)
        (observedSubstringFintype K) ≤
      (reconstructionSampleNorm K) ^ 2 := by
  letI : Fintype (ObservedSubstringNonterminal K) :=
    observedSubstringFintype K
  calc
    Fintype.card (ObservedSubstringNonterminal K) ≤
        Fintype.card (ReconstructionFactorSlot K) :=
      Fintype.card_le_of_injective
        (observedSubstringToSlot K)
        (observedSubstringToSlot_injective K)
    _ ≤ (reconstructionSampleNorm K) ^ 2 :=
      reconstructionFactorSlot_card_le_sq K

/-- Exact v116 rules B/U/L with a genuinely finite nonterminal carrier. -/
def finiteSubstringGrammar
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    BinaryNullableGrammar (ObservedSubstringNonterminal K) α where
  terminalRule A a := A.1 = [a]
  binaryRule A B C := A.1 = B.1 ++ C.1
  epsilonRule _ := False
  unitRule A B := SubstringUnaryRelated H K A.1 B.1

/-- Every substring derivation has a derivation from each observed-factor state. -/
theorem substringDerives_to_finiteCFG
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x w : Word α}
    (d : SubstringDerives H K x w) :
    ∀ hroot : ∃ p q : Word α, Observed K x p q,
      BinaryNullableDerives (finiteSubstringGrammar H K)
        (⟨x, hroot⟩ : ObservedSubstringNonterminal K) w := by
  induction d with
  | letter hobs =>
      intro _hroot
      exact BinaryNullableDerives.terminal rfl
  | @unary x y w hrel _d ih =>
      intro _hroot
      have hy : ∃ p q : Word α, Observed K y p q := by
        rcases hrel.2 with ⟨p, q, _hx, hy⟩
        exact ⟨p, q, hy⟩
      exact BinaryNullableDerives.unit hrel (ih hy)
  | @binary x y w₁ w₂ hparent hx hy _dx _dy ihx ihy =>
      intro _hroot
      rcases hparent with ⟨p, q, hp⟩
      have hleft : Observed K x p (y ++ q) := by
        constructor
        · exact hx
        · simpa only [List.append_assoc] using hp.2
      have hright : Observed K y (p ++ x) q := by
        constructor
        · exact hy
        · simpa only [List.append_assoc] using hp.2
      exact BinaryNullableDerives.binary rfl
        (ihx ⟨p, y ++ q, hleft⟩)
        (ihy ⟨p ++ x, q, hright⟩)

/-- Finite grammar derivations admit precisely the v116 substring rules. -/
theorem finiteCFG_to_substringDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A : ObservedSubstringNonterminal K} {w : Word α}
    (d : BinaryNullableDerives (finiteSubstringGrammar H K) A w) :
    SubstringDerives H K A.1 w := by
  induction d with
  | @terminal A a hterm =>
      have hobs : ∃ p q : Word α, Observed K [a] p q := by
        simpa [hterm] using A.2
      change A.1 = [a] at hterm
      rw [hterm]
      exact SubstringDerives.letter hobs
  | epsilon heps =>
      exact False.elim heps
  | unit hrel _d ih =>
      exact SubstringDerives.unary hrel ih
  | @binary A B C wB wC hbin _dB _dC ihB ihC =>
      have hparent : ∃ p q : Word α,
          Observed K (B.1 ++ C.1) p q := by
        rw [← hbin]
        exact A.2
      have hB := observedSubstring_ne_nil K B
      have hC := observedSubstring_ne_nil K C
      rw [hbin]
      exact SubstringDerives.binary hparent hB hC ihB ihC

/-- Start language of the genuinely finite v116 grammar, including epsilon. -/
def finiteSubstringBatchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Set (Word α) :=
  {w | (∃ A : ObservedSubstringNonterminal K,
       A.1 ∈ K ∧
       BinaryNullableDerives (finiteSubstringGrammar H K) A w) ∨
       (w = [] ∧ ([] : Word α) ∈ K)}

/-- Finite CFG start language equals substring semantics, even for empty K. -/
theorem finiteSubstringBatchLanguage_eq_substringBatchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    finiteSubstringBatchLanguage H K =
      SubstringBatchLanguage H K := by
  ext w
  change
    ((∃ A : ObservedSubstringNonterminal K, A.1 ∈ K ∧
       BinaryNullableDerives (finiteSubstringGrammar H K) A w) ∨
     (w = [] ∧ ([] : Word α) ∈ K)) ↔
    ((∃ s : Word α, s ∈ K ∧ s ≠ [] ∧
       SubstringDerives H K s w) ∨
     (w = [] ∧ ([] : Word α) ∈ K))
  constructor
  · rintro (⟨A, hs, hd⟩ | ⟨h0, heps⟩)
    · exact Or.inl ⟨A.1, hs, observedSubstring_ne_nil K A,
        finiteCFG_to_substringDerives H K hd⟩
    · exact Or.inr ⟨h0, heps⟩
  · rintro (⟨s, hs, hsne, hd⟩ | ⟨h0, heps⟩)
    · have hroot : ∃ p q : Word α, Observed K s p q := by
        exact ⟨[], [], ⟨hsne, by simpa using hs⟩⟩
      exact Or.inl ⟨⟨s, hroot⟩, hs,
        substringDerives_to_finiteCFG H K hd hroot⟩
    · exact Or.inr ⟨h0, heps⟩

/-- Full start-language equivalence to the archived v88 batch semantics. -/
theorem finiteSubstringBatchLanguage_eq_batchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    finiteSubstringBatchLanguage H K = BatchLanguage H K := by
  calc
    finiteSubstringBatchLanguage H K =
        SubstringBatchLanguage H K :=
      finiteSubstringBatchLanguage_eq_substringBatchLanguage H K
    _ = BatchLanguage H K :=
      substringBatchLanguage_eq_batchLanguage H K

end FiniteSubstring

end TCS1
end LeanCfgProject
