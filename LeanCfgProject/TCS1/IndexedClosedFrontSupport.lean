import LeanCfgProject.TCS1.FiniteCFGEncoding

/-!
# TCS #1 v66: rule-closure friendly finite front-end support

For the semantic binarization grammar it is useful to include every old
isolated state and only the suffix states that actually occur as suffixes of
finite source right-hand sides.  This support is still linear in the source
encoding size, but makes all old-state closure obligations immediate.

This module establishes the support's cardinality, activity, and the key
suffix-tail closure fact.  The next layer uses these facts to prove closure
under the actual binary grammar rules.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedClosedFrontSupport

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/--
All old isolated states, together with every source-RHS suffix beginning at an
actual production occurrence.
-/
def indexedClosedFrontSupport
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P) :
    Finset (FrontEndState N α) :=
  (Finset.univ.image
      (fun X : N ⊕ α => BinarizedState.old X))
    ∪
  (Finset.univ.image
      (fun o : ProductionOccurrence G =>
        BinarizedState.suffix (occurrenceSuffix G o)))

/-- Every old isolated state belongs to the closed front-end support. -/
theorem indexedClosedFrontSupport_old_mem
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (X : N ⊕ α) :
    BinarizedState.old X ∈ indexedClosedFrontSupport G := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr
    ⟨X, Finset.mem_univ _, rfl⟩

/-- Every occurrence suffix belongs to the closed front-end support. -/
theorem indexedClosedFrontSupport_suffix_mem
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (o : ProductionOccurrence G) :
    BinarizedState.suffix (occurrenceSuffix G o) ∈
      indexedClosedFrontSupport G := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr
    ⟨o, Finset.mem_univ _, rfl⟩

/-- A supported suffix state is represented by an actual production occurrence. -/
theorem indexedClosedFrontSupport_suffix_exists
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (xs : List (MixedSymbol N α))
    (hxs :
      BinarizedState.suffix xs ∈
        indexedClosedFrontSupport G) :
    ∃ o : ProductionOccurrence G,
      occurrenceSuffix G o = xs := by
  rcases Finset.mem_union.mp hxs with hold | hsuf
  · rcases Finset.mem_image.mp hold with
      ⟨X, hX, hEq⟩
    cases hEq
  · rcases Finset.mem_image.mp hsuf with
      ⟨o, ho, hEq⟩
    exact
      ⟨o, BinarizedState.suffix.inj hEq⟩

/--
If an occurrence suffix has at least two symbols, the tail is the suffix at
the successor occurrence and hence is supported.
-/
theorem indexedClosedFrontSupport_occurrence_tail_mem
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (o : ProductionOccurrence G)
    (B C : MixedSymbol N α)
    (rest : List (MixedSymbol N α))
    (hsuf :
      occurrenceSuffix G o = B :: C :: rest) :
    BinarizedState.suffix (C :: rest) ∈
      indexedClosedFrontSupport G := by
  have hlen :
      (G.rhs o.1).length - o.2.1 =
        (B :: C :: rest).length := by
    simpa [occurrenceSuffix, List.length_drop] using
      congrArg List.length hsuf
  have hnext :
      o.2.1 + 1 < (G.rhs o.1).length := by
    simp only [List.length_cons] at hlen
    omega
  let o' : ProductionOccurrence G :=
    ⟨o.1, ⟨o.2.1 + 1, hnext⟩⟩
  have hsuf' :
      occurrenceSuffix G o' = C :: rest := by
    unfold occurrenceSuffix o'
    change
      (G.rhs o.1).drop (o.2.1 + 1) =
        C :: rest
    rw [← List.tail_drop]
    have htail := congrArg List.tail hsuf
    simpa [occurrenceSuffix] using htail
  rw [← hsuf']
  exact indexedClosedFrontSupport_suffix_mem G o'

/-- Any supported suffix with at least two symbols has its tail supported. -/
theorem indexedClosedFrontSupport_suffix_tail_mem
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (B C : MixedSymbol N α)
    (rest : List (MixedSymbol N α))
    (hmem :
      BinarizedState.suffix (B :: C :: rest) ∈
        indexedClosedFrontSupport G) :
    BinarizedState.suffix (C :: rest) ∈
      indexedClosedFrontSupport G := by
  obtain ⟨o, ho⟩ :=
    indexedClosedFrontSupport_suffix_exists
      G (B :: C :: rest) hmem
  exact
    indexedClosedFrontSupport_occurrence_tail_mem
      G o B C rest ho

/--
The support has size at most all old isolated states plus one suffix slot per
source RHS occurrence.
-/
theorem indexedClosedFrontSupport_card_le
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P) :
    (indexedClosedFrontSupport G).card ≤
      Fintype.card N + Fintype.card α +
        G.totalRhsLength := by
  let oldPart : Finset (FrontEndState N α) :=
    Finset.univ.image
      (fun X : N ⊕ α => BinarizedState.old X)
  let suffixPart : Finset (FrontEndState N α) :=
    Finset.univ.image
      (fun o : ProductionOccurrence G =>
        BinarizedState.suffix (occurrenceSuffix G o))
  have hUnion :
      (indexedClosedFrontSupport G).card ≤
        oldPart.card + suffixPart.card := by
    simpa [indexedClosedFrontSupport, oldPart, suffixPart] using
      Finset.card_union_le oldPart suffixPart
  have hOld :
      oldPart.card ≤ Fintype.card (N ⊕ α) := by
    dsimp [oldPart]
    simpa using
      (Finset.card_image_le :
        (Finset.univ.image
          (fun X : N ⊕ α => BinarizedState.old X)).card
          ≤ (Finset.univ : Finset (N ⊕ α)).card)
  have hSuffix :
      suffixPart.card ≤ Fintype.card (ProductionOccurrence G) := by
    dsimp [suffixPart]
    simpa using
      (Finset.card_image_le :
        (Finset.univ.image
          (fun o : ProductionOccurrence G =>
            BinarizedState.suffix (occurrenceSuffix G o))).card
          ≤ (Finset.univ :
              Finset (ProductionOccurrence G)).card)
  calc
    (indexedClosedFrontSupport G).card
      ≤ oldPart.card + suffixPart.card := hUnion
    _ ≤ Fintype.card (N ⊕ α) +
        Fintype.card (ProductionOccurrence G) :=
      Nat.add_le_add hOld hSuffix
    _ = Fintype.card N + Fintype.card α +
        G.totalRhsLength := by
      rw [Fintype.card_sum, productionOccurrence_card G]

/--
If every source RHS has length at most n, every state in the closed support is
active for the semantic front-end length bound.
-/
theorem indexedClosedFrontSupport_active
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (n : Nat)
    (hRhs : ∀ p, (G.rhs p).length ≤ n) :
    ∀ X, X ∈ indexedClosedFrontSupport G →
      FrontEndActive (N := N) (α := α) n X := by
  intro X hX
  rcases Finset.mem_union.mp hX with hold | hsuf
  · rcases Finset.mem_image.mp hold with
      ⟨Y, hY, rfl⟩
    trivial
  · rcases Finset.mem_image.mp hsuf with
      ⟨o, ho, rfl⟩
    change (occurrenceSuffix G o).length ≤ n
    have hdrop :
        (occurrenceSuffix G o).length ≤
          (G.rhs o.1).length := by
      simp [occurrenceSuffix]
    exact le_trans hdrop (hRhs o.1)

end IndexedClosedFrontSupport

end TCS1
end LeanCfgProject
