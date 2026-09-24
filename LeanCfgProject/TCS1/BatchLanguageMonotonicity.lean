import LeanCfgProject.TCS1.ReconstructionSoundness

/-!
# TCS #1: monotonicity of set-driven reconstruction

The reconstruction grammar is monotone in its positive sample: enlarging the
sample can only add observed factors and start witnesses.  This elementary
fact is the bridge from a finite characteristic sample C to every later
accumulated sample K containing C in the Gold learner.

Combined with soundness, exact reconstruction from C therefore implies exact
reconstruction from every positive super-sample K.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BatchLanguageMonotonicity

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- An observed occurrence stays observed when the sample is enlarged. -/
theorem observed_mono
    {K K' : Finset (Word α)}
    (hKK : K ⊆ K')
    {x u v : Word α}
    (hobs : Observed K x u v) :
    Observed K' x u v :=
  ⟨hobs.1, hKK hobs.2⟩

/-- Every non-start reconstruction derivation survives enlargement of K. -/
theorem hypDerives_mono
    (H : FixedFiniteMonoidHom α M)
    {K K' : Finset (Word α)}
    (hKK : K ⊆ K')
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    HypDerives H K' x u v w := by
  induction d with
  | r4 hobs =>
      exact HypDerives.r4 (observed_mono hKK hobs)
  | r3 hobs hobs' htype d ih =>
      exact
        HypDerives.r3
          (observed_mono hKK hobs)
          (observed_mono hKK hobs')
          htype ih
  | r2 hobs hobs' d ih =>
      exact
        HypDerives.r2
          (observed_mono hKK hobs)
          (observed_mono hKK hobs')
          ih
  | r1 hparent hleft hright dleft dright ihleft ihrigh =>
      exact
        HypDerives.r1
          (observed_mono hKK hparent)
          (observed_mono hKK hleft)
          (observed_mono hKK hright)
          ihleft ihrigh

/-- Start derivations are monotone in the positive sample as well. -/
theorem batchDerives_mono
    (H : FixedFiniteMonoidHom α M)
    {K K' : Finset (Word α)}
    (hKK : K ⊆ K')
    {w : Word α}
    (d : BatchDerives H K w) :
    BatchDerives H K' w := by
  cases d with
  | nonempty hs hs_ne d =>
      exact
        BatchDerives.nonempty
          (hKK hs) hs_ne
          (hypDerives_mono H hKK d)
  | epsilon heps =>
      exact BatchDerives.epsilon (hKK heps)

/-- The reconstructed language is monotone under sample inclusion. -/
theorem batchLanguage_mono
    (H : FixedFiniteMonoidHom α M)
    {K K' : Finset (Word α)}
    (hKK : K ⊆ K') :
    BatchLanguage H K ⊆ BatchLanguage H K' := by
  intro w hw
  exact batchDerives_mono H hKK hw

/--
Characteristicity is upward closed among positive samples.

If C already reconstructs L exactly, then every finite K with
C subseteq K subseteq L also reconstructs L exactly.
-/
theorem batchLanguage_exact_of_characteristic_subset
    (H : FixedFiniteMonoidHom α M)
    (C K : Finset (Word α))
    (L : Set (Word α))
    (hCK : C ⊆ K)
    (hKL : (↑K : Set (Word α)) ⊆ L)
    (hsub : FixedHSubstitutable H L)
    (hchar : BatchLanguage H C = L) :
    BatchLanguage H K = L := by
  apply Set.Subset.antisymm
  · exact batchLanguage_sound H K L hKL hsub
  · rw [← hchar]
    exact batchLanguage_mono H hCK

end BatchLanguageMonotonicity

end TCS1
end LeanCfgProject
