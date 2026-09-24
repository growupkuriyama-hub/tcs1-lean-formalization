import LeanCfgProject.TCS1.WitnessSetConstruction
import LeanCfgProject.TCS1.ReducedTypedRuleBridge
import LeanCfgProject.TCS1.FixedWindowCharacteristicDataBounds

/-!
# TCS #1 v68: cardinality of the canonical witness set

The fixed-window size theorem counts four witness families:

* one anchor for each active typed nonterminal;
* one witness for each active typed terminal production;
* one witness for each active typed binary production; and
* at most one epsilon witness.

This file connects that paper count to the actual
`canonicalWitnessFinset` used by the reconstruction development.  Possible
collisions between witness words only decrease the cardinality.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section CanonicalWitnessCounting

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/-- Untyped terminal productions of the underlying SSBNF grammar. -/
abbrev UntypedTerminalRuleIndex
    (terminalRule : N → α → Prop) :=
  {p : N × α // terminalRule p.1 p.2}

/-- Untyped binary productions of the underlying SSBNF grammar. -/
abbrev UntypedBinaryRuleIndex
    (binaryRule : N → N → N → Prop) :=
  {p : N × N × N //
    binaryRule p.1 p.2.1 p.2.2}

/-- Active typed terminal productions, counted once each. -/
abbrev ActiveTypedTerminalIndex
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (Active : N × M → Prop) :=
  {p : N × α //
    terminalRule p.1 p.2 ∧
      Active (p.1, H.h [p.2])}

/-- Active typed binary productions, counted once for each pair of child types. -/
abbrev ActiveTypedBinaryIndex
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop) :=
  {p : (N × N × N) × (M × M) //
    binaryRule p.1.1 p.1.2.1 p.1.2.2 ∧
      Active (p.1.1, p.2.1 * p.2.2) ∧
      Active (p.1.2.1, p.2.1) ∧
      Active (p.1.2.2, p.2.2)}

/-- One finite indexing type covering all four canonical witness families. -/
abbrev CanonicalWitnessIndex
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop) :=
  Sum
    (ActiveTypedSymbol Active)
    (Sum
      (ActiveTypedTerminalIndex H terminalRule Active)
      (Sum
        (ActiveTypedBinaryIndex binaryRule Active)
        Unit))

/-- Word represented by one witness-family index. -/
def canonicalWitnessIndexWord
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    CanonicalWitnessIndex H terminalRule binaryRule Active →
      Word α
  | Sum.inl X =>
      C.left X.1 ++ C.omega X.1 ++ C.right X.1
  | Sum.inr (Sum.inl p) =>
      C.left (p.1.1, H.h [p.1.2]) ++
        [p.1.2] ++
        C.right (p.1.1, H.h [p.1.2])
  | Sum.inr (Sum.inr (Sum.inl p)) =>
      C.left (p.1.1.1, p.1.2.1 * p.1.2.2) ++
        C.omega (p.1.1.2.1, p.1.2.1) ++
        C.omega (p.1.1.2.2, p.1.2.2) ++
        C.right (p.1.1.1, p.1.2.1 * p.1.2.2)
  | Sum.inr (Sum.inr (Sum.inr _)) =>
      []

/-- Active typed symbols are a subset of the full N-by-M product. -/
theorem activeTypedSymbol_card_le
    [Fintype N]
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)] :
    Fintype.card (ActiveTypedSymbol Active) ≤
      Fintype.card N * Fintype.card M := by
  have h :=
    Fintype.card_le_of_injective
      (fun X : ActiveTypedSymbol Active => X.1)
      Subtype.val_injective
  simpa using h

/-- Typed terminal productions inject into underlying terminal productions. -/
theorem activeTypedTerminalIndex_card_le
    [Fintype N] [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (Active : N × M → Prop)
    [Fintype (ActiveTypedTerminalIndex H terminalRule Active)]
    [Fintype (UntypedTerminalRuleIndex terminalRule)] :
    Fintype.card
        (ActiveTypedTerminalIndex H terminalRule Active) ≤
      Fintype.card
        (UntypedTerminalRuleIndex terminalRule) := by
  let forget :
      ActiveTypedTerminalIndex H terminalRule Active →
        UntypedTerminalRuleIndex terminalRule :=
    fun p => ⟨p.1, p.2.1⟩
  have hinj : Function.Injective forget := by
    intro x y h
    apply Subtype.ext
    have hv :
        (forget x).1 = (forget y).1 :=
      congrArg
        (fun z : UntypedTerminalRuleIndex terminalRule => z.1)
        h
    simpa [forget] using hv
  exact
    Fintype.card_le_of_injective forget hinj

/--
Typed binary productions inject into an underlying binary production together
with the two child monoid types.
-/
theorem activeTypedBinaryIndex_card_le
    [Fintype N]
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop)
    [Fintype (ActiveTypedBinaryIndex binaryRule Active)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)] :
    Fintype.card
        (ActiveTypedBinaryIndex binaryRule Active) ≤
      Fintype.card
          (UntypedBinaryRuleIndex binaryRule) *
        (Fintype.card M)^2 := by
  let forget :
      ActiveTypedBinaryIndex binaryRule Active →
        UntypedBinaryRuleIndex binaryRule × (M × M) :=
    fun p =>
      (⟨p.1.1, p.2.1⟩, p.1.2)
  have hinj : Function.Injective forget := by
    intro x y h
    apply Subtype.ext
    exact
      congrArg
        (fun z :
          UntypedBinaryRuleIndex binaryRule × (M × M) =>
            (z.1.1, z.2))
        h
  have hcard :=
    Fintype.card_le_of_injective forget hinj
  simpa [pow_two] using hcard

/--
Every actual canonical witness word is the image of one family index.
The Unit summand harmlessly covers epsilon even when epsilon is absent.
-/
theorem canonicalWitnessFinset_card_le_index
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    [Fintype (ActiveTypedTerminalIndex H terminalRule Active)]
    [Fintype (ActiveTypedBinaryIndex binaryRule Active)]
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    (canonicalWitnessFinset
      H terminalRule binaryRule startRule epsilonStart Active C).card
      ≤
    Fintype.card
      (CanonicalWitnessIndex
        H terminalRule binaryRule Active) := by
  classical
  let f :=
    canonicalWitnessIndexWord
      H terminalRule binaryRule startRule epsilonStart Active C
  let cover :
      Finset (Word α) :=
    Finset.univ.image f

  have hsub :
      canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C
        ⊆ cover := by
    intro word hword
    have hw :
        word ∈
          CanonicalWitnessWords
            H terminalRule binaryRule startRule epsilonStart Active C :=
      (mem_canonicalWitnessFinset_iff
        H terminalRule binaryRule startRule epsilonStart Active C word).1
        hword
    rcases hw with
      ⟨X, hX, rfl⟩
      | ⟨A, a, hterm, hactive, rfl⟩
      | ⟨A, B, Cn, μ, ν, hbin, hA, hB, hC, rfl⟩
      | ⟨heps, rfl⟩
    · apply Finset.mem_image.mpr
      refine
        ⟨Sum.inl (⟨X, hX⟩ : ActiveTypedSymbol Active),
          Finset.mem_univ _, ?_⟩
      rfl
    · apply Finset.mem_image.mpr
      refine
        ⟨Sum.inr
            (Sum.inl
              (⟨(A, a), ⟨hterm, hactive⟩⟩ :
                ActiveTypedTerminalIndex H terminalRule Active)),
          Finset.mem_univ _, ?_⟩
      rfl
    · apply Finset.mem_image.mpr
      refine
        ⟨Sum.inr
            (Sum.inr
              (Sum.inl
                (⟨((A, (B, Cn)), (μ, ν)),
                    ⟨hbin, hA, hB, hC⟩⟩ :
                  ActiveTypedBinaryIndex binaryRule Active))),
          Finset.mem_univ _, ?_⟩
      rfl
    · apply Finset.mem_image.mpr
      refine
        ⟨Sum.inr (Sum.inr (Sum.inr Unit.unit)),
          Finset.mem_univ _, ?_⟩
      rfl

  have hcardCover :
      cover.card ≤
        Fintype.card
          (CanonicalWitnessIndex
            H terminalRule binaryRule Active) := by
    dsimp [cover]
    simpa using
      (Finset.card_image_le
        (s :=
          (Finset.univ :
            Finset
              (CanonicalWitnessIndex
                H terminalRule binaryRule Active)))
        (f := f))

  exact
    le_trans
      (Finset.card_le_card hsub)
      hcardCover

/-- Paper-facing four-family cardinality bound. -/
theorem canonicalWitnessFinset_card_le_families
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    [Fintype (ActiveTypedTerminalIndex H terminalRule Active)]
    [Fintype (ActiveTypedBinaryIndex binaryRule Active)]
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    (canonicalWitnessFinset
      H terminalRule binaryRule startRule epsilonStart Active C).card
      ≤
    Fintype.card (ActiveTypedSymbol Active) +
      Fintype.card
        (ActiveTypedTerminalIndex H terminalRule Active) +
      Fintype.card
        (ActiveTypedBinaryIndex binaryRule Active) +
      1 := by
  have h :=
    canonicalWitnessFinset_card_le_index
      H terminalRule binaryRule startRule epsilonStart Active C
  simp only [CanonicalWitnessIndex, Fintype.card_sum,
    Fintype.card_unit] at h
  omega

/--
The actual canonical witness finset satisfies the fixed-window encoded-size
envelope as soon as its words satisfy the Lemma 7.2 length bound.

Here the abstract arithmetic parameters of
`fixedWindow_sampleNorm_bound` are instantiated by the genuine active typed
symbols and production-index types.
-/
theorem canonicalWitnessFinset_fixedWindow_sampleNorm_bound
    [Fintype α] [DecidableEq α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    [Fintype (ActiveTypedTerminalIndex H terminalRule Active)]
    [Fintype (ActiveTypedBinaryIndex binaryRule Active)]
    [Fintype (UntypedTerminalRuleIndex terminalRule)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)]
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (r τG : Nat)
    (hlen :
      ∀ w ∈
        canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C,
        w.length ≤
          fixedWindowWitnessLengthEnvelope
            (Fintype.card (ActiveTypedSymbol Active))
            r (Fintype.card N) τG) :
    (∑ w ∈
      canonicalWitnessFinset
        H terminalRule binaryRule startRule epsilonStart Active C,
      (w.length + 1)) ≤
    fixedWindowCharacteristicEnvelope
      (Fintype.card M)
      r
      (Fintype.card N)
      (Fintype.card (UntypedTerminalRuleIndex terminalRule))
      (Fintype.card (UntypedBinaryRuleIndex binaryRule))
      τG := by
  let K :=
    canonicalWitnessFinset
      H terminalRule binaryRule startRule epsilonStart Active C

  have hNt :
      Fintype.card (ActiveTypedSymbol Active) ≤
        Fintype.card N * Fintype.card M :=
    activeTypedSymbol_card_le Active

  have ht :
      Fintype.card
          (ActiveTypedTerminalIndex H terminalRule Active) ≤
        Fintype.card
          (UntypedTerminalRuleIndex terminalRule) :=
    activeTypedTerminalIndex_card_le
      H terminalRule Active

  have hb :
      Fintype.card
          (ActiveTypedBinaryIndex binaryRule Active) ≤
        Fintype.card
          (UntypedBinaryRuleIndex binaryRule) *
            (Fintype.card M)^2 :=
    activeTypedBinaryIndex_card_le
      binaryRule Active

  have hcard :
      K.card ≤
        Fintype.card (ActiveTypedSymbol Active) +
          Fintype.card
            (ActiveTypedTerminalIndex H terminalRule Active) +
          Fintype.card
            (ActiveTypedBinaryIndex binaryRule Active) +
          1 := by
    dsimp [K]
    exact
      canonicalWitnessFinset_card_le_families
        H terminalRule binaryRule startRule epsilonStart Active C

  apply
    fixedWindow_sampleNorm_bound
      K
      (m := Fintype.card M)
      (r := r)
      (N := Fintype.card N)
      (t := Fintype.card
        (UntypedTerminalRuleIndex terminalRule))
      (b := Fintype.card
        (UntypedBinaryRuleIndex binaryRule))
      (τG := τG)
      (Nt := Fintype.card (ActiveTypedSymbol Active))
      (tTyped := Fintype.card
        (ActiveTypedTerminalIndex H terminalRule Active))
      (bTyped := Fintype.card
        (ActiveTypedBinaryIndex binaryRule Active))
      hNt ht hb hcard
  intro w hw
  exact hlen w hw

end CanonicalWitnessCounting

end TCS1
end LeanCfgProject
