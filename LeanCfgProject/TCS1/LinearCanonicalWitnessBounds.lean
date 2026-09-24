import LeanCfgProject.TCS1.LinearSpineBounds
import LeanCfgProject.TCS1.CanonicalWitnessCounting

/-!
# TCS #1: linear canonical-witness size package

This module connects the linear-spine shortness bounds to the actual
canonical witness finset used by the reconstruction theorem.

The semantic linear-spine argument only has to establish two uniform facts on
active typed symbols:

* the chosen productive yield has length at most n_t; and
* the chosen terminal reaching context has total length at most 2 n_t.

From those two facts, all four witness families have a common O(n_t) length
bound.  Combining that with the already verified four-family witness count
gives an explicit polynomial encoded-size envelope for the linear subclass.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearCanonicalWitnessBounds

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/--
Explicit encoded-size envelope for linear canonical data.

N is the number of underlying non-start symbols, m the fixed monoid size,
and t,b the underlying terminal/binary production counts.  Since the number
of active typed symbols is at most N*m, every canonical witness has length at
most 4*(N*m)+1.
-/
def linearCharacteristicEnvelope
    (m N t b : Nat) : Nat :=
  witnessCountEnvelope N t b m *
    (linearCanonicalWitnessLengthEnvelope (N * m) + 1)

/--
If productive yields and reaching contexts obey the linear-spine bounds, every
word of the actual canonical witness finset has the common linear length
envelope.
-/
theorem mem_canonicalWitnessFinset_linear_length_le
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (n_t : Nat)
    (homega :
      ∀ X, Active X →
        (C.omega X).length ≤ n_t)
    (hcontext :
      ∀ X, Active X →
        (C.left X).length + (C.right X).length ≤
          2 * n_t)
    {word : Word α}
    (hword :
      word ∈
        canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C) :
    word.length ≤
      linearCanonicalWitnessLengthEnvelope n_t := by
  classical
  have hw :
      word ∈
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart Active C :=
    (mem_canonicalWitnessFinset_iff
      H terminalRule binaryRule startRule epsilonStart Active C word).1
      hword
  rcases hw with
    ⟨X, hX, rfl⟩
    | ⟨A, a, hterm, hA, rfl⟩
    | ⟨A, B, Cn, μ, ν, hbin, hA, hB, hC, rfl⟩
    | ⟨heps, rfl⟩
  · exact
      linear_anchorWitness_length_le_envelope
        (hcontext X hX)
        (homega X hX)
  · exact
      linear_terminalWitness_length_le_envelope
        (a := a)
        (hcontext (A, H.h [a]) hA)
  · exact
      linear_binaryWitness_length_le_envelope
        (hcontext (A, μ * ν) hA)
        (homega (B, μ) hB)
        (homega (Cn, ν) hC)
  · simp [linearCanonicalWitnessLengthEnvelope]

/--
The linear witness-length envelope is monotone in the typed-symbol bound.
-/
theorem linearCanonicalWitnessLengthEnvelope_mono
    {a b : Nat}
    (hab : a ≤ b) :
    linearCanonicalWitnessLengthEnvelope a ≤
      linearCanonicalWitnessLengthEnvelope b := by
  unfold linearCanonicalWitnessLengthEnvelope
  omega

/--
Full encoded-size bound for the actual canonical witness finset.

This theorem uses the actual active typed-symbol cardinality as n_t and then
eliminates it using n_t ≤ |N|*|M|.  The terminal and binary typed-rule counts
are eliminated by the existing canonical-witness counting lemmas.
-/
theorem canonicalWitnessFinset_linear_norm_le
    [Fintype α] [DecidableEq α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (homega :
      ∀ X, Active X →
        (C.omega X).length ≤
          @Fintype.card
            (ActiveTypedSymbol Active)
            (Fintype.ofFinite _))
    (hcontext :
      ∀ X, Active X →
        (C.left X).length + (C.right X).length ≤
          2 *
            @Fintype.card
              (ActiveTypedSymbol Active)
              (Fintype.ofFinite _)) :
    (∑ word ∈
      canonicalWitnessFinset
        H terminalRule binaryRule startRule epsilonStart Active C,
      (word.length + 1))
      ≤
    linearCharacteristicEnvelope
      (Fintype.card M)
      (Fintype.card N)
      (@Fintype.card
        (UntypedTerminalRuleIndex terminalRule)
        (Fintype.ofFinite _))
      (@Fintype.card
        (UntypedBinaryRuleIndex binaryRule)
        (Fintype.ofFinite _)) := by
  classical
  let Nt :=
    @Fintype.card
      (ActiveTypedSymbol Active)
      (Fintype.ofFinite _)
  let tTyped :=
    @Fintype.card
      (ActiveTypedTerminalIndex H terminalRule Active)
      (Fintype.ofFinite _)
  let bTyped :=
    @Fintype.card
      (ActiveTypedBinaryIndex binaryRule Active)
      (Fintype.ofFinite _)
  let t :=
    @Fintype.card
      (UntypedTerminalRuleIndex terminalRule)
      (Fintype.ofFinite _)
  let b :=
    @Fintype.card
      (UntypedBinaryRuleIndex binaryRule)
      (Fintype.ofFinite _)

  letI : Fintype (ActiveTypedSymbol Active) :=
    Fintype.ofFinite _
  letI :
      Fintype
        (ActiveTypedTerminalIndex H terminalRule Active) :=
    Fintype.ofFinite _
  letI :
      Fintype
        (ActiveTypedBinaryIndex binaryRule Active) :=
    Fintype.ofFinite _
  letI : Fintype (UntypedTerminalRuleIndex terminalRule) :=
    Fintype.ofFinite _
  letI : Fintype (UntypedBinaryRuleIndex binaryRule) :=
    Fintype.ofFinite _

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
          (Fintype.card M) ^ 2 :=
    activeTypedBinaryIndex_card_le
      binaryRule Active
  have hcardFamilies :
      (canonicalWitnessFinset
        H terminalRule binaryRule startRule epsilonStart Active C).card
        ≤
      Fintype.card (ActiveTypedSymbol Active) +
        Fintype.card
          (ActiveTypedTerminalIndex H terminalRule Active) +
        Fintype.card
          (ActiveTypedBinaryIndex binaryRule Active) +
        1 :=
    canonicalWitnessFinset_card_le_families
      H terminalRule binaryRule startRule epsilonStart Active C
  have hcard :
      (canonicalWitnessFinset
        H terminalRule binaryRule startRule epsilonStart Active C).card
        ≤
      witnessCountEnvelope
        (Fintype.card N)
        (Fintype.card
          (UntypedTerminalRuleIndex terminalRule))
        (Fintype.card
          (UntypedBinaryRuleIndex binaryRule))
        (Fintype.card M) := by
    exact le_trans hcardFamilies
      (witnessCount_le_envelope hNt ht hb)

  have hlenNt :
      ∀ word ∈
        canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C,
        word.length ≤
          linearCanonicalWitnessLengthEnvelope
            (Fintype.card (ActiveTypedSymbol Active)) := by
    intro word hword
    exact
      mem_canonicalWitnessFinset_linear_length_le
        H terminalRule binaryRule startRule epsilonStart Active C
        (Fintype.card (ActiveTypedSymbol Active))
        (by
          intro X hX
          simpa [Nt] using homega X hX)
        (by
          intro X hX
          simpa [Nt] using hcontext X hX)
        hword

  have hlenMono :
      linearCanonicalWitnessLengthEnvelope
          (Fintype.card (ActiveTypedSymbol Active))
        ≤
      linearCanonicalWitnessLengthEnvelope
        (Fintype.card N * Fintype.card M) :=
    linearCanonicalWitnessLengthEnvelope_mono hNt

  have hlen :
      ∀ word ∈
        canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C,
        word.length ≤
          linearCanonicalWitnessLengthEnvelope
            (Fintype.card N * Fintype.card M) := by
    intro word hword
    exact le_trans (hlenNt word hword) hlenMono

  unfold linearCharacteristicEnvelope
  exact
    sampleNorm_le_of_card_and_length
      (canonicalWitnessFinset
        H terminalRule binaryRule startRule epsilonStart Active C)
      (witnessCountEnvelope
        (Fintype.card N)
        (Fintype.card
          (UntypedTerminalRuleIndex terminalRule))
        (Fintype.card
          (UntypedBinaryRuleIndex binaryRule))
        (Fintype.card M))
      (linearCanonicalWitnessLengthEnvelope
        (Fintype.card N * Fintype.card M))
      hcard hlen

end LinearCanonicalWitnessBounds

end TCS1
end LeanCfgProject
