import LeanCfgProject.TCS1.WitnessSetConstruction
import LeanCfgProject.TCS1.FixedWindowContextPathBound
import LeanCfgProject.TCS1.FixedWindowLemma71ReducedFacade

/-!
# TCS #1 v68: paper-facing arithmetic facade for Lemma 7.2

Lemma 7.2 has two layers.  The semantic layer supplies, for each surviving
typed symbol, a canonical typed yield of length at most B and a canonical
reaching context of total length at most Nt*B.  The witness-set layer then
checks the four witness families.

This file closes the second layer directly against the actual
`CanonicalWitnessWords` definition used by the completeness development.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section FixedWindowLemma72Facade

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/--
Minimality assumptions for the canonical choices used in Section 7.

The manuscript chooses `omega(X)` shortlex-minimally and `chi(X)`
minimum-length among terminal reaching contexts.  Only the displayed length
minimality consequences are needed for the quantitative proof.
-/
structure CanonicalChoiceMinimality
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) : Prop where
  omega_minimal :
    ∀ X : N × M,
      Active X →
      ∀ z : Word α,
        ReducedTypedDerives
          H terminalRule binaryRule Active X z →
        (C.omega X).length ≤ z.length
  context_minimal :
    ∀ X : N × M,
      Active X →
      ∀ left right : Word α,
        (∀ {z : Word α},
          ReducedTypedDerives
            H terminalRule binaryRule Active X z →
          ReducedTypedLanguage
            H terminalRule binaryRule startRule epsilonStart Active
            (left ++ z ++ right)) →
        (C.left X).length + (C.right X).length ≤
          left.length + right.length

/-- Quantitative data needed from Lemmas 7.1 and the first half of Lemma 7.2. -/
structure CanonicalYieldContextBounds
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (Nt B : Nat) : Prop where
  omega_bound :
    ∀ X : N × M,
      Active X →
      (C.omega X).length ≤ B
  context_bound :
    ∀ X : N × M,
      Active X →
      (C.left X).length + (C.right X).length ≤ Nt * B

/--
Bounded alternative yields and reaching contexts transfer to the canonical
minimal choices.
-/
theorem canonicalYieldContextBounds_of_bounded_alternatives
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    (Nt B : Nat)
    (hyield :
      ∀ X : N × M,
        Active X →
        ∃ z : Word α,
          ReducedTypedDerives
            H terminalRule binaryRule Active X z
          ∧ z.length ≤ B)
    (hcontext :
      ∀ X : N × M,
        Active X →
        ∃ left right : Word α,
          (∀ {z : Word α},
            ReducedTypedDerives
              H terminalRule binaryRule Active X z →
            ReducedTypedLanguage
              H terminalRule binaryRule startRule epsilonStart Active
              (left ++ z ++ right))
          ∧ left.length + right.length ≤ Nt * B) :
    CanonicalYieldContextBounds
      H terminalRule binaryRule startRule epsilonStart Active C Nt B := by
  constructor
  · intro X hX
    obtain ⟨z, dz, hz⟩ := hyield X hX
    exact le_trans
      (minimal.omega_minimal X hX z dz) hz
  · intro X hX
    obtain ⟨left, right, hreach, hlen⟩ :=
      hcontext X hX
    exact le_trans
      (minimal.context_minimal X hX left right hreach)
      hlen

/--
Lemma 7.1 supplies the canonical-yield half of the quantitative data needed
for Lemma 7.2.
-/
theorem canonicalOmega_length_le_fixedWindow
    [Fintype N] [DecidableEq N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    (trim :
      SuccessfulTypedTrimClosure
        H terminalRule binaryRule Active)
    (k l : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ) :
    ∀ X : N × M,
      Active X →
      (C.omega X).length ≤
        fixedWindowTypedYieldBound
          (k + l) (Fintype.card N) τ := by
  intro X hX
  exact
    fixedWindow_reduced_minimal_typed_yield_length_le
      H terminalRule binaryRule Active trim
      (C.omegaDerives X hX)
      (minimal.omega_minimal X hX)
      k l hrespect τ hshort

/--
Once bounded alternative reaching contexts are available, Lemma 7.1 plus
canonical minimality gives the complete quantitative data package used in the
witness-length proof.
-/
theorem canonicalYieldContextBounds_fixedWindow_of_context_alternatives
    [Fintype N] [DecidableEq N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    (trim :
      SuccessfulTypedTrimClosure
        H terminalRule binaryRule Active)
    (k l Nt : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hcontext :
      ∀ X : N × M,
        Active X →
        ∃ left right : Word α,
          (∀ {z : Word α},
            ReducedTypedDerives
              H terminalRule binaryRule Active X z →
            ReducedTypedLanguage
              H terminalRule binaryRule startRule epsilonStart Active
              (left ++ z ++ right))
          ∧
          left.length + right.length ≤
            Nt *
              fixedWindowTypedYieldBound
                (k + l) (Fintype.card N) τ) :
    CanonicalYieldContextBounds
      H terminalRule binaryRule startRule epsilonStart Active C
      Nt
      (fixedWindowTypedYieldBound
        (k + l) (Fintype.card N) τ) := by
  constructor
  · exact
      canonicalOmega_length_le_fixedWindow
        H terminalRule binaryRule startRule epsilonStart
        Active C minimal trim
        k l hrespect τ hshort
  · intro X hX
    obtain ⟨left, right, hreach, hlen⟩ :=
      hcontext X hX
    exact le_trans
      (minimal.context_minimal X hX left right hreach)
      hlen

/--
All four canonical witness families satisfy the common
`(Nt+2)B+1` envelope.
-/
theorem canonicalWitnessWords_length_le_common
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (Nt B : Nat)
    (bounds :
      CanonicalYieldContextBounds
        H terminalRule binaryRule startRule epsilonStart
        Active C Nt B)
    {word : Word α}
    (hword :
      word ∈
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart
          Active C) :
    word.length ≤ (Nt + 2) * B + 1 := by
  rcases hword with
    ⟨X, hX, rfl⟩
    | ⟨A, a, hterm, hA, rfl⟩
    | ⟨A, Bn, Cn, μ, ν, hbin, hA, hB, hC, rfl⟩
    | ⟨heps, rfl⟩
  · simp only [List.length_append]
    have hctx :=
      bounds.context_bound X hX
    have hω :=
      bounds.omega_bound X hX
    have hshape :
        (C.left X).length +
            (C.omega X).length +
            (C.right X).length =
          ((C.left X).length + (C.right X).length) +
            (C.omega X).length := by
      ring
    rw [hshape]
    exact
      anchor_witness_length_le_common
        hctx hω
  · simp only [List.length_append, List.length_singleton]
    have hctx :=
      bounds.context_bound (A, H.h [a]) hA
    have hshape :
        (C.left (A, H.h [a])).length + 1 +
            (C.right (A, H.h [a])).length =
          (C.left (A, H.h [a])).length +
            (C.right (A, H.h [a])).length + 1 := by
      ring
    rw [hshape]
    exact terminal_witness_length_le_common hctx
  · simp only [List.length_append]
    have hctx :=
      bounds.context_bound (A, μ * ν) hA
    have hωB :=
      bounds.omega_bound (Bn, μ) hB
    have hωC :=
      bounds.omega_bound (Cn, ν) hC
    have hshape :
        (C.left (A, μ * ν)).length +
              (C.omega (Bn, μ)).length +
              (C.omega (Cn, ν)).length +
              (C.right (A, μ * ν)).length =
          ((C.left (A, μ * ν)).length +
              (C.right (A, μ * ν)).length) +
            (C.omega (Bn, μ)).length +
            (C.omega (Cn, ν)).length := by
      ring
    rw [hshape]
    exact
      binary_witness_length_le_common
        hctx hωB hωC
  · simp

/--
Fixed-window specialization of the common witness envelope.

This is the second displayed conclusion of Lemma 7.2:
every word in W(tilde G) has length at most
`(Nt+2) B_{k,l}(G) + 1`.
-/
theorem canonicalWitnessWords_length_le_fixedWindow
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (Nt r Ncount τG : Nat)
    (bounds :
      CanonicalYieldContextBounds
        H terminalRule binaryRule startRule epsilonStart Active C
        Nt (fixedWindowTypedYieldBound r Ncount τG))
    {word : Word α}
    (hword :
      word ∈
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart
          Active C) :
    word.length ≤
      fixedWindowWitnessLengthEnvelope Nt r Ncount τG := by
  unfold fixedWindowWitnessLengthEnvelope
  exact
    canonicalWitnessWords_length_le_common
      H terminalRule binaryRule startRule epsilonStart Active C
      Nt (fixedWindowTypedYieldBound r Ncount τG)
      bounds hword

/--
Paper-facing conditional completion of Lemma 7.2.

The only remaining semantic input is the existence, for every active typed
symbol, of some terminal reaching context of the displayed Nt*B length.
Canonical context minimality then transfers that bound, Lemma 7.1 supplies
the canonical yield bound, and every actual witness word satisfies the common
envelope.
-/
theorem canonicalWitnessWords_length_le_fixedWindow_of_context_alternatives
    [Fintype N] [DecidableEq N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    (trim :
      SuccessfulTypedTrimClosure
        H terminalRule binaryRule Active)
    (k l Nt : Nat)
    (hrespect :
      RespectsFixedWindowSummary H k l)
    (τ : Nat)
    (hshort :
      ∀ A : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule A z
          ∧ z.length ≤ τ)
    (hcontext :
      ∀ X : N × M,
        Active X →
        ∃ left right : Word α,
          (∀ {z : Word α},
            ReducedTypedDerives
              H terminalRule binaryRule Active X z →
            ReducedTypedLanguage
              H terminalRule binaryRule startRule epsilonStart Active
              (left ++ z ++ right))
          ∧
          left.length + right.length ≤
            Nt *
              fixedWindowTypedYieldBound
                (k + l) (Fintype.card N) τ)
    {word : Word α}
    (hword :
      word ∈
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart Active C) :
    word.length ≤
      fixedWindowWitnessLengthEnvelope
        Nt (k + l) (Fintype.card N) τ := by
  have bounds :=
    canonicalYieldContextBounds_fixedWindow_of_context_alternatives
      H terminalRule binaryRule startRule epsilonStart
      Active C minimal trim
      k l Nt hrespect τ hshort hcontext
  exact
    canonicalWitnessWords_length_le_fixedWindow
      H terminalRule binaryRule startRule epsilonStart
      Active C
      Nt (k + l) (Fintype.card N) τ
      bounds hword

end FixedWindowLemma72Facade

end TCS1
end LeanCfgProject
