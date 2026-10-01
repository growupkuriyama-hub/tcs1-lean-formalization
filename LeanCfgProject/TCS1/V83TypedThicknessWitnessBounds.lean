import LeanCfgProject.TCS1.ConcreteTypedTrimming
import LeanCfgProject.TCS1.CanonicalWitnessCounting

/-!
# TCS #1 v83: typed-thickness witness bounds

The v83 manuscript replaces the former open ordinary-thickness question by
two separate statements.  This file formalizes the positive half: once every
surviving typed symbol has a canonical yield of length at most tau, shortest
dependency paths give contexts of length at most (Nt-1)*tau and all canonical
witness words have length at most (Nt+1)*tau.

The proof is independent of fixed-window summaries.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V83TypedThicknessWitnessBounds

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}

/--
Exact v83 dependency-path count: a repetition-free reaching spine over a
finite nonterminal universe has at most |N|-1 binary steps.
-/
theorem reachingSpine_siblings_length_le_card_sub_one
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings)
    (hnodup : path.Nodup) :
    siblings.length ≤ Fintype.card N - 1 := by
  have hvertices : path.length ≤ Fintype.card N :=
    dependency_path_vertices_le path hnodup
  have hsteps :
      siblings.length + 1 = path.length :=
    reachingSpine_siblings_length_add_one_eq_path
      terminalRule binaryRule spine
  omega

/--
Exact v83 context estimate for a repetition-free spine with B-bounded
off-path sibling yields.
-/
theorem reachingSpine_context_length_le_card_sub_one
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (B : Nat)
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings)
    (hnodup : path.Nodup)
    (heach : ∀ s ∈ siblings, s ≤ B) :
    left.length + right.length ≤
      (Fintype.card N - 1) * B := by
  have hcount :
      siblings.length ≤ Fintype.card N - 1 :=
    reachingSpine_siblings_length_le_card_sub_one
      terminalRule binaryRule spine hnodup
  have hsum :
      siblings.sum ≤ (Fintype.card N - 1) * B :=
    chainExpansion_sum_le
      siblings (Fintype.card N - 1) B hcount heach
  rw [reachingSpine_context_length_eq
    terminalRule binaryRule spine]
  exact hsum

/--
Cycle shortening plus the exact edge count gives a concrete context bounded
by (|N|-1)*B.
-/
theorem reachingSpine_nodup_context_exists_card_sub_one
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (B : Nat)
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings)
    (heach : ∀ s ∈ siblings, s ≤ B) :
    ∃ left' right' path' siblings',
      ReachingSpine terminalRule binaryRule
        A X left' right' path' siblings'
      ∧ path'.Nodup
      ∧ (∀ s ∈ siblings', s ≤ B)
      ∧ left'.length + right'.length ≤
          (Fintype.card N - 1) * B := by
  obtain ⟨left', right', path', siblings',
      spine', hnodup, heach'⟩ :=
    normalize_reachingSpine_to_nodup
      terminalRule binaryRule B spine heach
  refine
    ⟨left', right', path', siblings',
      spine', hnodup, heach', ?_⟩
  exact
    reachingSpine_context_length_le_card_sub_one
      terminalRule binaryRule B
      spine' hnodup heach'

/--
Canonical minimum contexts inherit the exact v83 context bound from
structural reachability whenever all canonical productive yields are
B-bounded.
-/
theorem canonicalContext_length_le_of_typedYieldBound
    [Fintype N]
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (B : Nat)
    (hω :
      ∀ X : N × M,
        Active X →
        (C.omega X).length ≤ B)
    (X : N × M)
    (hX : Active X) :
    (C.left X).length + (C.right X).length ≤
      (Fintype.card (ActiveTypedSymbol Active) - 1) * B := by
  classical
  letI : DecidableEq (ActiveTypedSymbol Active) := Classical.decEq _

  let XT : ActiveTypedSymbol Active := ⟨X, hX⟩
  obtain ⟨R, left₀, right₀, path₀, siblings₀,
      hstart, spine₀⟩ :=
    reach.spine XT

  have hshort :
      ∀ (Y : ActiveTypedSymbol Active) {z₀ : Word α},
        UntypedDerives
          (ActiveTypedTerminalRule H terminalRule Active)
          (ActiveTypedBinaryRule binaryRule Active)
          Y z₀ →
        ∃ z : Word α,
          UntypedDerives
            (ActiveTypedTerminalRule H terminalRule Active)
            (ActiveTypedBinaryRule binaryRule Active)
            Y z
          ∧ z.length ≤ B := by
    intro Y z₀ _d₀
    let z := C.omega Y.1
    have dzReduced :
        ReducedTypedDerives
          H terminalRule binaryRule Active
          Y.1 z :=
      C.omegaDerives Y.1 Y.2
    have dzActiveRaw :=
      reducedTypedDerives_to_activeUntypedDerives
        H terminalRule binaryRule Active dzReduced
    have dzActive :
        UntypedDerives
          (ActiveTypedTerminalRule H terminalRule Active)
          (ActiveTypedBinaryRule binaryRule Active)
          Y z := by
      simpa [z] using dzActiveRaw
    exact ⟨z, dzActive, hω Y.1 Y.2⟩

  obtain ⟨left₁, right₁, siblings₁,
      spine₁, heach₁⟩ :=
    reachingSpine_replace_siblings_by_bounded_yields
      (ActiveTypedTerminalRule H terminalRule Active)
      (ActiveTypedBinaryRule binaryRule Active)
      B spine₀ hshort

  obtain ⟨left', right', path', siblings',
      spine', hnodup, heach', hlen⟩ :=
    reachingSpine_nodup_context_exists_card_sub_one
      (ActiveTypedTerminalRule H terminalRule Active)
      (ActiveTypedBinaryRule binaryRule Active)
      B spine₁ heach₁

  have hreach :
      ∀ {z : Word α},
        ReducedTypedDerives
          H terminalRule binaryRule Active X z →
        ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active
          (left' ++ z ++ right') := by
    intro z dX
    have dXActiveRaw :=
      reducedTypedDerives_to_activeUntypedDerives
        H terminalRule binaryRule Active dX
    have dXActive :
        UntypedDerives
          (ActiveTypedTerminalRule H terminalRule Active)
          (ActiveTypedBinaryRule binaryRule Active)
          XT z := by
      simpa [XT] using dXActiveRaw
    have dRootActive :
        UntypedDerives
          (ActiveTypedTerminalRule H terminalRule Active)
          (ActiveTypedBinaryRule binaryRule Active)
          R (left' ++ z ++ right') :=
      reachingSpine_plug
        (ActiveTypedTerminalRule H terminalRule Active)
        (ActiveTypedBinaryRule binaryRule Active)
        spine' dXActive
    have dRootReduced :
        ReducedTypedDerives
          H terminalRule binaryRule Active
          R.1 (left' ++ z ++ right') :=
      activeUntypedDerives_to_reducedTypedDerives
        H terminalRule binaryRule Active dRootActive
    exact
      ReducedTypedStartDerives.nonempty
        hstart R.2 dRootReduced

  exact le_trans
    (minimal.context_minimal X hX left' right' hreach)
    hlen

/--
The three non-epsilon witness families satisfy the exact v83 common envelope
(Nt+1)*B once canonical contexts are bounded by (Nt-1)*B and B is positive.
-/
theorem canonicalWitnessWords_length_le_typedThickness
    [Fintype N]
    (Active : N × M → Prop)
    [Fintype (ActiveTypedSymbol Active)]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (B : Nat)
    (hB : 1 ≤ B)
    (hω :
      ∀ X : N × M,
        Active X →
        (C.omega X).length ≤ B)
    {word : Word α}
    (hword :
      word ∈
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart Active C) :
    word.length ≤
      (Fintype.card (ActiveTypedSymbol Active) + 1) * B := by
  classical
  let Nt := Fintype.card (ActiveTypedSymbol Active)
  rcases hword with
    ⟨X, hX, rfl⟩
    | ⟨A, a, hterm, hA, rfl⟩
    | ⟨A, Bn, Cn, μ, ν, hbin, hA, hBn, hCn, rfl⟩
    | ⟨heps, rfl⟩
  · have hNt : 0 < Nt := by
      have hnonempty : Nonempty (ActiveTypedSymbol Active) :=
        ⟨⟨X, hX⟩⟩
      exact Fintype.card_pos
    have hctx :=
      canonicalContext_length_le_of_typedYieldBound
        Active H terminalRule binaryRule startRule epsilonStart
        C minimal reach B hω X hX
    have hωX := hω X hX
    simp only [List.length_append]
    change
      (C.left X).length + (C.omega X).length +
          (C.right X).length ≤ (Nt + 1) * B
    have hshape :
        (C.left X).length + (C.omega X).length +
            (C.right X).length =
          ((C.left X).length + (C.right X).length) +
            (C.omega X).length := by ring
    rw [hshape]
    calc
      (C.left X).length + (C.right X).length +
          (C.omega X).length
        ≤ (Nt - 1) * B + B := Nat.add_le_add hctx hωX
      _ ≤ (Nt + 1) * B := by
        have hpred : Nt - 1 + 1 = Nt := by omega
        calc
          (Nt - 1) * B + B = (Nt - 1 + 1) * B := by ring
          _ = Nt * B := by rw [hpred]
          _ ≤ (Nt + 1) * B :=
            Nat.mul_le_mul_right B (Nat.le_succ Nt)
  · have hNt : 0 < Nt := by
      have hnonempty : Nonempty (ActiveTypedSymbol Active) :=
        ⟨⟨(A, H.h [a]), hA⟩⟩
      exact Fintype.card_pos
    have hctx :=
      canonicalContext_length_le_of_typedYieldBound
        Active H terminalRule binaryRule startRule epsilonStart
        C minimal reach B hω (A, H.h [a]) hA
    simp only [List.length_append, List.length_singleton]
    have hshape :
        (C.left (A, H.h [a])).length + 1 +
            (C.right (A, H.h [a])).length =
          ((C.left (A, H.h [a])).length +
            (C.right (A, H.h [a])).length) + 1 := by ring
    rw [hshape]
    calc
      (C.left (A, H.h [a])).length +
          (C.right (A, H.h [a])).length + 1
        ≤ (Nt - 1) * B + 1 := Nat.add_le_add_right hctx 1
      _ ≤ (Nt - 1) * B + B :=
        Nat.add_le_add_left hB ((Nt - 1) * B)
      _ ≤ (Nt + 1) * B := by
        have hpred : Nt - 1 + 1 = Nt := by omega
        calc
          (Nt - 1) * B + B = (Nt - 1 + 1) * B := by ring
          _ = Nt * B := by rw [hpred]
          _ ≤ (Nt + 1) * B :=
            Nat.mul_le_mul_right B (Nat.le_succ Nt)
  · have hNt : 0 < Nt := by
      have hnonempty : Nonempty (ActiveTypedSymbol Active) :=
        ⟨⟨(A, μ * ν), hA⟩⟩
      exact Fintype.card_pos
    have hctx :=
      canonicalContext_length_le_of_typedYieldBound
        Active H terminalRule binaryRule startRule epsilonStart
        C minimal reach B hω (A, μ * ν) hA
    have hωB := hω (Bn, μ) hBn
    have hωC := hω (Cn, ν) hCn
    simp only [List.length_append]
    have hshape :
        (C.left (A, μ * ν)).length +
            (C.omega (Bn, μ)).length +
            (C.omega (Cn, ν)).length +
            (C.right (A, μ * ν)).length =
          ((C.left (A, μ * ν)).length +
            (C.right (A, μ * ν)).length) +
            (C.omega (Bn, μ)).length +
            (C.omega (Cn, ν)).length := by ring
    rw [hshape]
    calc
      (C.left (A, μ * ν)).length +
          (C.right (A, μ * ν)).length +
          (C.omega (Bn, μ)).length +
          (C.omega (Cn, ν)).length
        ≤ (Nt - 1) * B + B + B := by
          exact Nat.add_le_add
            (Nat.add_le_add hctx hωB) hωC
      _ = (Nt + 1) * B := by
        have hpred : Nt - 1 + 2 = Nt + 1 := by omega
        calc
          (Nt - 1) * B + B + B =
              (Nt - 1 + 2) * B := by ring
          _ = (Nt + 1) * B := by rw [hpred]
  · simp

/-- Explicit v83 witness-count envelope. -/
def typedThicknessWitnessCountEnvelope
    (m N t b : Nat) : Nat :=
  N * m + t + b * m^2 + 1

/--
The actual canonical witness finset is bounded by the four-family count used
in the v83 displayed inequality.
-/
theorem canonicalWitnessFinset_card_le_typedThicknessEnvelope
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
    [Fintype (UntypedTerminalRuleIndex terminalRule)]
    [Fintype (UntypedBinaryRuleIndex binaryRule)]
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    (canonicalWitnessFinset
      H terminalRule binaryRule startRule epsilonStart Active C).card
      ≤
    typedThicknessWitnessCountEnvelope
      (Fintype.card M)
      (Fintype.card N)
      (Fintype.card (UntypedTerminalRuleIndex terminalRule))
      (Fintype.card (UntypedBinaryRuleIndex binaryRule)) := by
  have hNt :=
    activeTypedSymbol_card_le Active
  have ht :=
    activeTypedTerminalIndex_card_le
      H terminalRule Active
  have hb :=
    activeTypedBinaryIndex_card_le
      binaryRule Active
  have hcard :=
    canonicalWitnessFinset_card_le_families
      H terminalRule binaryRule startRule epsilonStart Active C
  unfold typedThicknessWitnessCountEnvelope
  omega

/--
Encoded-size form of the v83 typed-thickness witness bound.
-/
theorem canonicalWitnessFinset_sampleNorm_le_typedThickness
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
    (minimal :
      CanonicalChoiceMinimality
        H terminalRule binaryRule startRule epsilonStart Active C)
    (reach :
      ActiveTypedStructuralReachability
        H terminalRule binaryRule startRule Active)
    (τ : Nat)
    (hτ : 1 ≤ τ)
    (hω :
      ∀ X : N × M,
        Active X →
        (C.omega X).length ≤ τ) :
    (∑ w ∈
      canonicalWitnessFinset
        H terminalRule binaryRule startRule epsilonStart Active C,
      (w.length + 1)) ≤
    typedThicknessWitnessCountEnvelope
      (Fintype.card M)
      (Fintype.card N)
      (Fintype.card (UntypedTerminalRuleIndex terminalRule))
      (Fintype.card (UntypedBinaryRuleIndex binaryRule))
      *
      (((Fintype.card N * Fintype.card M + 1) * τ) + 1) := by
  let K :=
    canonicalWitnessFinset
      H terminalRule binaryRule startRule epsilonStart Active C
  let W :=
    typedThicknessWitnessCountEnvelope
      (Fintype.card M)
      (Fintype.card N)
      (Fintype.card (UntypedTerminalRuleIndex terminalRule))
      (Fintype.card (UntypedBinaryRuleIndex binaryRule))
  let L := (Fintype.card N * Fintype.card M + 1) * τ

  have hcard : K.card ≤ W := by
    dsimp [K, W]
    exact
      canonicalWitnessFinset_card_le_typedThicknessEnvelope
        H terminalRule binaryRule startRule epsilonStart Active C

  have hNt :
      Fintype.card (ActiveTypedSymbol Active) ≤
        Fintype.card N * Fintype.card M :=
    activeTypedSymbol_card_le Active

  have hlen :
      ∀ w ∈ K, w.length ≤ L := by
    intro w hw
    have hwWords :
        w ∈
          CanonicalWitnessWords
            H terminalRule binaryRule startRule epsilonStart Active C :=
      (mem_canonicalWitnessFinset_iff
        H terminalRule binaryRule startRule epsilonStart Active C w).1 hw
    have h0 :=
      canonicalWitnessWords_length_le_typedThickness
        Active H terminalRule binaryRule startRule epsilonStart
        C minimal reach τ hτ hω hwWords
    dsimp [L]
    exact le_trans h0
      (Nat.mul_le_mul_right τ
        (Nat.add_le_add_right hNt 1))

  have hnorm :=
    sampleNorm_le_of_card_and_length
      K W L hcard hlen
  simpa [K, W, L] using hnorm

end V83TypedThicknessWitnessBounds

end TCS1
end LeanCfgProject
