import LeanCfgProject.TCS1.FrontEndFiniteSupportFacade
import Mathlib.Data.Fintype.BigOperators

/-!
# TCS #1 v66: finite indexed CFG encoding for the normalization front end

This module introduces a concrete finite encoding layer for the source CFG.
Productions are indexed by a finite type P; each production carries a left
nonterminal and a finite mixed right-hand side.

For cardinality bookkeeping we use a deliberately generous front-end state
universe.  Besides the original nonterminals it contains two copies of every
right-hand-side occurrence: one copy is available for terminal wrappers and
one for suffix states.  This may contain unused states, but its size is exactly

  |N| + 2 * (total RHS length),

hence linear in any reasonable grammar encoding.

Each generous state maps into the ambient semantic front-end state type.
Taking the image of the finite universe gives a concrete finite support.  Its
cardinality is bounded by the same linear expression, and every support state
satisfies the front-end length bound whenever each source RHS has length at
most the encoding-size parameter n.

The only remaining obligation for a complete support certificate is rule
closure; that is handled separately.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section FiniteIndexedCFGEncoding

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- Finite indexed presentation of a mixed CFG. -/
structure IndexedMixedCFG
    (N : Type u)
    (α : Type v)
    (P : Type w) where
  lhs : P → N
  rhs : P → List (MixedSymbol N α)

/-- Predicate-style grammar presented by the finite production index. -/
def IndexedMixedCFG.toMixedRules
    (G : IndexedMixedCFG N α P) :
    MixedRules N α :=
  fun A rhs =>
    ∃ p, G.lhs p = A ∧ G.rhs p = rhs

/-- Total number of symbol occurrences in all right-hand sides. -/
def IndexedMixedCFG.totalRhsLength
    [Fintype P]
    (G : IndexedMixedCFG N α P) : Nat :=
  ∑ p : P, (G.rhs p).length

/-- One source right-hand-side occurrence, with its production provenance. -/
abbrev ProductionOccurrence
    (G : IndexedMixedCFG N α P) :=
  Sigma (fun p : P => Fin (G.rhs p).length)

/-- Symbol stored at a production occurrence. -/
def occurrenceSymbol
    (G : IndexedMixedCFG N α P)
    (o : ProductionOccurrence G) :
    MixedSymbol N α :=
  (G.rhs o.1).get o.2

/-- Suffix of the source RHS beginning at a given occurrence. -/
def occurrenceSuffix
    (G : IndexedMixedCFG N α P)
    (o : ProductionOccurrence G) :
    List (MixedSymbol N α) :=
  (G.rhs o.1).drop o.2.1

/--
A generous finite state universe: original nonterminals, one wrapper slot per
RHS occurrence, and one suffix slot per RHS occurrence.
-/
abbrev GenerousFrontState
    [Fintype N] [Fintype P]
    (G : IndexedMixedCFG N α P) :=
  N ⊕ (ProductionOccurrence G ⊕ ProductionOccurrence G)

/-- The occurrence type has cardinality equal to total RHS length. -/
@[simp] theorem productionOccurrence_card
    [Fintype P]
    (G : IndexedMixedCFG N α P) :
    Fintype.card (ProductionOccurrence G) =
      G.totalRhsLength := by
  simp [ProductionOccurrence,
    IndexedMixedCFG.totalRhsLength]

/-- Exact cardinality of the generous front-end state universe. -/
@[simp] theorem generousFrontState_card
    [Fintype N] [Fintype P]
    (G : IndexedMixedCFG N α P) :
    Fintype.card (GenerousFrontState G) =
      Fintype.card N + 2 * G.totalRhsLength := by
  rw [Fintype.card_sum, Fintype.card_sum]
  rw [productionOccurrence_card G]
  omega

/--
Map the generous finite universe into the ambient semantic front-end state
type.  A wrapper occurrence maps to the old isolated state named by its source
symbol; a suffix occurrence maps to the corresponding source suffix.
-/
def generousFrontEmbed
    [Fintype N] [Fintype P]
    (G : IndexedMixedCFG N α P) :
    GenerousFrontState G → FrontEndState N α
  | Sum.inl A =>
      BinarizedState.old (Sum.inl A)
  | Sum.inr (Sum.inl o) =>
      BinarizedState.old (occurrenceSymbol G o)
  | Sum.inr (Sum.inr o) =>
      BinarizedState.suffix (occurrenceSuffix G o)

/-- Finite support obtained as the image of the generous state universe. -/
def indexedFrontSupport
    [Fintype N] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P) :
    Finset (FrontEndState N α) :=
  Finset.univ.image (generousFrontEmbed G)

/-- The finite support is no larger than the generous state universe. -/
theorem indexedFrontSupport_card_le
    [Fintype N] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P) :
    (indexedFrontSupport G).card ≤
      Fintype.card N + 2 * G.totalRhsLength := by
  have himage :
      (indexedFrontSupport G).card ≤
        (Finset.univ : Finset (GenerousFrontState G)).card := by
    unfold indexedFrontSupport
    exact Finset.card_image_le
  calc
    (indexedFrontSupport G).card
        ≤ Fintype.card (GenerousFrontState G) := by
          simpa using himage
    _ = Fintype.card N + 2 * G.totalRhsLength :=
      generousFrontState_card G

/--
A convenient grammar-size scale for the finite indexed presentation.
-/
def IndexedMixedCFG.encodingScale
    [Fintype N] [Fintype P]
    (G : IndexedMixedCFG N α P) : Nat :=
  Fintype.card N +
    Fintype.card P +
    G.totalRhsLength

/-- The generous front-end support is linear in the indexed encoding scale. -/
theorem indexedFrontSupport_card_le_twice_scale
    [Fintype N] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P) :
    (indexedFrontSupport G).card ≤
      2 * G.encodingScale := by
  have hcard :=
    indexedFrontSupport_card_le G
  unfold IndexedMixedCFG.encodingScale
  omega

/--
Every embedded generous state is active whenever every source RHS length is at
most n.
-/
theorem generousFrontEmbed_active
    [Fintype N] [Fintype P]
    (G : IndexedMixedCFG N α P)
    (n : Nat)
    (hRhs : ∀ p, (G.rhs p).length ≤ n)
    (X : GenerousFrontState G) :
    FrontEndActive (N := N) (α := α) n
      (generousFrontEmbed G X) := by
  cases X with
  | inl A =>
      trivial
  | inr Y =>
      cases Y with
      | inl o =>
          trivial
      | inr o =>
          change (occurrenceSuffix G o).length ≤ n
          have hlen :
              (occurrenceSuffix G o).length ≤
                (G.rhs o.1).length := by
            simp [occurrenceSuffix]
          exact le_trans hlen (hRhs o.1)

/-- Hence every member of the finite image support is active. -/
theorem indexedFrontSupport_active
    [Fintype N] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (n : Nat)
    (hRhs : ∀ p, (G.rhs p).length ≤ n) :
    ∀ X, X ∈ indexedFrontSupport G →
      FrontEndActive (N := N) (α := α) n X := by
  intro X hX
  rcases Finset.mem_image.mp hX with
    ⟨Y, hY, rfl⟩
  exact generousFrontEmbed_active G n hRhs Y

end FiniteIndexedCFGEncoding

end TCS1
end LeanCfgProject
