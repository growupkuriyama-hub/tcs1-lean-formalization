import LeanCfgProject.TCS1.ReconstructionCFGPresentation
import LeanCfgProject.TCS1.ReconstructionFiniteCandidateSpaces

/-!
# TCS #1 v79: finite support for reconstruction nonterminals

The ordinary CFG presentation of R1--R4 uses the paper-facing symbols
`[x;u,v]`.  For a fixed finite sample only observed symbols can participate.
This module makes that support genuinely finite.

An active symbol is encoded by

* the sampled whole word `uxv`, and
* the two cut positions `|u|` and `|u|+|x|`.

The key is finite because the sample is finite and both cuts are bounded by
the encoded sample norm.  The encoding is injective, so the active
reconstruction-state type receives a concrete Fintype and an explicit
cardinality bound.  This is the semantic counterpart of the earlier generous
two-cut occurrence count.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section ReconstructionFiniteStateSupport

variable {α : Type u}
variable [DecidableEq α]

/-- Reconstruction symbols that are actually observed in the finite sample. -/
abbrev ActiveReconstructionNonterminal
    (K : Finset (Word α)) :=
  {q : ReconstructionNonterminal α //
    Observed K q.factor q.leftContext q.rightContext}

/--
A finite global key for one active reconstruction symbol.

The two cut coordinates use the sample norm as a common bound; this is
slightly more generous than the dependent two-cut occurrence space but makes
the injective finite encoding transparent.
-/
abbrev ReconstructionActiveStateKey
    (K : Finset (Word α)) :=
  ReconstructionSampleWord K ×
    (Fin (reconstructionSampleNorm K + 1) ×
      Fin (reconstructionSampleNorm K + 1))

/-- Every sampled word contributes at most its own encoding to the sample norm. -/
theorem reconstructionSampleWord_encoding_le_norm
    (K : Finset (Word α))
    {w : Word α}
    (hw : w ∈ K) :
    w.length + 1 ≤ reconstructionSampleNorm K := by
  classical
  unfold reconstructionSampleNorm
  exact
    Finset.single_le_sum
      (fun z hz => Nat.zero_le (z.length + 1))
      hw

/-- Encode an observed `[x;u,v]` by its sampled whole word and two cuts. -/
def reconstructionActiveStateKey
    (K : Finset (Word α))
    (q : ActiveReconstructionNonterminal K) :
    ReconstructionActiveStateKey K := by
  let x := q.1.factor
  let u := q.1.leftContext
  let v := q.1.rightContext
  let whole : Word α := u ++ x ++ v
  have hwhole : whole ∈ K := by
    simpa [whole, x, u, v] using q.2.2
  have henc :
      whole.length + 1 ≤ reconstructionSampleNorm K :=
    reconstructionSampleWord_encoding_le_norm K hwhole
  have huWhole : u.length ≤ whole.length := by
    simp [whole]
  have hjWhole : u.length + x.length ≤ whole.length := by
    simp [whole]
  have hi :
      u.length < reconstructionSampleNorm K + 1 := by
    omega
  have hj :
      u.length + x.length <
        reconstructionSampleNorm K + 1 := by
    omega
  exact
    (⟨whole, hwhole⟩,
      (⟨u.length, hi⟩,
        ⟨u.length + x.length, hj⟩))

/-- The finite occurrence key remembers the reconstruction symbol uniquely. -/
theorem reconstructionActiveStateKey_injective
    (K : Finset (Word α)) :
    Function.Injective
      (reconstructionActiveStateKey
        (α := α) K) := by
  intro A B hkey
  rcases A with ⟨⟨x₁, u₁, v₁⟩, hobs₁⟩
  rcases B with ⟨⟨x₂, u₂, v₂⟩, hobs₂⟩
  have hwhole :
      u₁ ++ x₁ ++ v₁ =
        u₂ ++ x₂ ++ v₂ := by
    have h :=
      congrArg
        (fun z : ReconstructionActiveStateKey K =>
          (z.1 : Word α))
        hkey
    simpa [reconstructionActiveStateKey] using h
  have huLen :
      u₁.length = u₂.length := by
    have h :=
      congrArg
        (fun z : ReconstructionActiveStateKey K =>
          z.2.1.1)
        hkey
    simpa [reconstructionActiveStateKey] using h
  have huxLen :
      u₁.length + x₁.length =
        u₂.length + x₂.length := by
    have h :=
      congrArg
        (fun z : ReconstructionActiveStateKey K =>
          z.2.2.1)
        hkey
    simpa [reconstructionActiveStateKey] using h
  have hxLen :
      x₁.length = x₂.length := by
    omega
  have hu : u₁ = u₂ := by
    calc
      u₁ =
          (u₁ ++ x₁ ++ v₁).take u₁.length := by
            simp
      _ =
          (u₂ ++ x₂ ++ v₂).take u₁.length := by
            rw [hwhole]
      _ =
          (u₂ ++ x₂ ++ v₂).take u₂.length := by
            rw [huLen]
      _ = u₂ := by
            simp
  have htail :
      x₁ ++ v₁ = x₂ ++ v₂ := by
    calc
      x₁ ++ v₁ =
          (u₁ ++ x₁ ++ v₁).drop u₁.length := by
            simp
      _ =
          (u₂ ++ x₂ ++ v₂).drop u₁.length := by
            rw [hwhole]
      _ =
          (u₂ ++ x₂ ++ v₂).drop u₂.length := by
            rw [huLen]
      _ = x₂ ++ v₂ := by
            simp
  have hx : x₁ = x₂ := by
    calc
      x₁ =
          (x₁ ++ v₁).take x₁.length := by
            simp
      _ =
          (x₂ ++ v₂).take x₁.length := by
            rw [htail]
      _ =
          (x₂ ++ v₂).take x₂.length := by
            rw [hxLen]
      _ = x₂ := by
            simp
  have hv : v₁ = v₂ := by
    calc
      v₁ =
          (x₁ ++ v₁).drop x₁.length := by
            simp
      _ =
          (x₂ ++ v₂).drop x₁.length := by
            rw [htail]
      _ =
          (x₂ ++ v₂).drop x₂.length := by
            rw [hxLen]
      _ = v₂ := by
            simp
  apply Subtype.ext
  cases hu
  cases hx
  cases hv
  rfl

/-- Concrete finite structure on the observed reconstruction symbols. -/
noncomputable def activeReconstructionNonterminalFintype
    (K : Finset (Word α)) :
    Fintype (ActiveReconstructionNonterminal K) :=
  Fintype.ofInjective
    (reconstructionActiveStateKey
      (α := α) K)
    (reconstructionActiveStateKey_injective
      (α := α) K)

/-- Exact cardinality of the generous global key space. -/
theorem reconstructionActiveStateKey_card_eq
    (K : Finset (Word α)) :
    Fintype.card (ReconstructionActiveStateKey K) =
      K.card * (reconstructionSampleNorm K + 1) ^ 2 := by
  classical
  simp [ReconstructionActiveStateKey,
    reconstructionSampleWord_card_eq,
    pow_two, Nat.mul_assoc]

/-- The active paper-facing reconstruction state set is genuinely finite. -/
theorem activeReconstructionNonterminal_card_le_key
    (K : Finset (Word α)) :
    @Fintype.card
        (ActiveReconstructionNonterminal K)
        (activeReconstructionNonterminalFintype K)
      ≤
    Fintype.card (ReconstructionActiveStateKey K) := by
  letI : Fintype (ActiveReconstructionNonterminal K) :=
    activeReconstructionNonterminalFintype K
  exact
    Fintype.card_le_of_injective
      (reconstructionActiveStateKey
        (α := α) K)
      (reconstructionActiveStateKey_injective
        (α := α) K)


/--
The global finite key space is already bounded by the direct output-encoding
envelope.  The extra factor (n+1) in that envelope absorbs the common cut
coordinate bound without needing any case split at n=0.
-/
theorem reconstructionActiveStateKey_card_le_outputEncodingEnvelope
    (K : Finset (Word α)) :
    Fintype.card (ReconstructionActiveStateKey K) ≤
      reconstructionOutputEncodingEnvelope
        (reconstructionSampleNorm K) := by
  rw [reconstructionActiveStateKey_card_eq]
  let n := reconstructionSampleNorm K
  have hK : K.card ≤ n := by
    simpa [n] using reconstructionSample_card_le_norm K
  have hmul :
      K.card * (n + 1) ^ 2 ≤
        n * (n + 1) ^ 2 :=
    Nat.mul_le_mul_right _ hK
  have hbase :
      n * (n + 1) ≤
        reconstructionRuleCandidateEnvelope n := by
    unfold reconstructionRuleCandidateEnvelope
    nlinarith [Nat.zero_le (n ^ 3), Nat.zero_le (n ^ 4)]
  have hscaled :
      n * (n + 1) ^ 2 ≤
        reconstructionRuleCandidateEnvelope n * (n + 1) := by
    calc
      n * (n + 1) ^ 2
          = (n * (n + 1)) * (n + 1) := by ring
      _ ≤
        reconstructionRuleCandidateEnvelope n * (n + 1) :=
          Nat.mul_le_mul_right (n + 1) hbase
  simpa [n, reconstructionOutputEncodingEnvelope] using
    (le_trans hmul hscaled)

/--
The actual observed reconstruction-state count is bounded by the same explicit
stored-grammar encoding envelope used by the CYK cost layer.
-/
theorem activeReconstructionNonterminal_card_le_outputEncodingEnvelope
    (K : Finset (Word α)) :
    @Fintype.card
        (ActiveReconstructionNonterminal K)
        (activeReconstructionNonterminalFintype K)
      ≤
    reconstructionOutputEncodingEnvelope
      (reconstructionSampleNorm K) := by
  exact le_trans
    (activeReconstructionNonterminal_card_le_key
      (α := α) K)
    (reconstructionActiveStateKey_card_le_outputEncodingEnvelope
      (α := α) K)

end ReconstructionFiniteStateSupport

end TCS1
end LeanCfgProject
