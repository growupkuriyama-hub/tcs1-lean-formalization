import LeanCfgProject.TCS1.V115InverseHomClosure
import LeanCfgProject.TCS1.V115CFGHomomorphicImage

/-!
# TCS #1 v115: factorization of arbitrary inverse homomorphic images

For phi : Gamma* -> Sigma*, introduce the intermediate alphabet Gamma + Sigma.
Encode each source letter b as

  inl(b) · map inr (phi(b)).

Let f erase all inl letters and retain inr Sigma letters, and let pi retain
the inl Gamma letters and erase the inr letters.  Then

  phi^{-1}(L) = pi( D_phi ∩ f^{-1}(L) ),

where D_phi is exactly the set of concatenations of encoded source letters.

This module proves the factorization as an exact language identity.  The two
remaining CFL obligations are deliberately separate:
(1) f^{-1}(L) is CFL by a free-insertion grammar;
(2) D_phi is regular by a finite automaton.
The final projection pi is covered by V115CFGHomomorphicImage.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V115InverseHomReduction

variable {α : Type u} {β : Type v}

/-- Encode one input letter together with its complete homomorphic output. -/
def v115InverseEncodingLetter
    (φ : β → Word α)
    (b : β) :
    Word (β ⊕ α) :=
  Sum.inl b :: (φ b).map Sum.inr

/-- Erase source markers and retain output letters. -/
def v115IntermediateErase :
    β ⊕ α → Word α
  | Sum.inl _ => []
  | Sum.inr a => [a]

/-- Retain source markers and erase output letters. -/
def v115IntermediateProject :
    β ⊕ α → Word β
  | Sum.inl b => [b]
  | Sum.inr _ => []

/-- Encode a complete input word block by block. -/
def v115InverseEncoding
    (φ : β → Word α)
    (w : Word β) :
    Word (β ⊕ α) :=
  v115WordSubstitution
    (v115InverseEncodingLetter φ) w

@[simp] theorem v115IntermediateErase_encodingLetter
    (φ : β → Word α)
    (b : β) :
    v115WordSubstitution
      (v115IntermediateErase (α := α) (β := β))
      (v115InverseEncodingLetter φ b)
      =
    φ b := by
  have hmap (xs : Word α) :
      (xs.map Sum.inr).flatMap
        (v115IntermediateErase (α := α) (β := β)) = xs := by
    induction xs with
    | nil => rfl
    | cons a rest ih =>
        simp [v115IntermediateErase, ih]
  simpa [v115InverseEncodingLetter,
    v115IntermediateErase, v115WordSubstitution] using hmap (φ b)

@[simp] theorem v115IntermediateProject_encodingLetter
    (φ : β → Word α)
    (b : β) :
    v115WordSubstitution
      (v115IntermediateProject (α := α) (β := β))
      (v115InverseEncodingLetter φ b)
      =
    [b] := by
  simp [v115InverseEncodingLetter,
    v115IntermediateProject, v115WordSubstitution]

/-- Erasing an encoded block word recovers precisely phi(w). -/
theorem v115IntermediateErase_encoding
    (φ : β → Word α)
    (w : Word β) :
    v115WordSubstitution
      (v115IntermediateErase (α := α) (β := β))
      (v115InverseEncoding φ w)
      =
    v115WordSubstitution φ w := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      change
        v115WordSubstitution
          (v115IntermediateErase (α := α) (β := β))
          (v115InverseEncodingLetter φ b ++
            v115InverseEncoding φ rest)
          =
        φ b ++ v115WordSubstitution φ rest
      rw [v115WordSubstitution_append,
        v115IntermediateErase_encodingLetter, ih]

/-- Projecting an encoded block word recovers the original input word. -/
theorem v115IntermediateProject_encoding
    (φ : β → Word α)
    (w : Word β) :
    v115WordSubstitution
      (v115IntermediateProject (α := α) (β := β))
      (v115InverseEncoding φ w)
      =
    w := by
  induction w with
  | nil =>
      rfl
  | cons b rest ih =>
      change
        v115WordSubstitution
          (v115IntermediateProject (α := α) (β := β))
          (v115InverseEncodingLetter φ b ++
            v115InverseEncoding φ rest)
          =
        b :: rest
      rw [v115WordSubstitution_append,
        v115IntermediateProject_encodingLetter, ih]
      rfl

/-- D_phi: valid concatenations of complete encoded source-letter blocks. -/
def v115InverseEncodingLanguage
    (φ : β → Word α) :
    Set (Word (β ⊕ α)) :=
  {v | ∃ w : Word β,
    v115InverseEncoding φ w = v}

/-- f^{-1}(L) for the erasing intermediate projection f. -/
def v115IntermediateErasePreimage
    (L : Set (Word α)) :
    Set (Word (β ⊕ α)) :=
  {v |
    v115WordSubstitution
      (v115IntermediateErase (α := α) (β := β)) v
      ∈ L}

/-- Homomorphic image under the projection pi retaining source markers. -/
def v115IntermediateProjectedImage
    (K : Set (Word (β ⊕ α))) :
    Set (Word β) :=
  {w | ∃ v,
    v ∈ K ∧
    v115WordSubstitution
      (v115IntermediateProject (α := α) (β := β)) v
      = w}

/--
Exact standard factorization used for CFL inverse-homomorphism closure.
No context-free closure theorem is assumed in this identity.
-/
theorem v115SubstitutionPreimage_factorization
    (φ : β → Word α)
    (L : Set (Word α)) :
    v115SubstitutionPreimage φ L
      =
    v115IntermediateProjectedImage
      (v115InverseEncodingLanguage φ
        ∩ v115IntermediateErasePreimage
            (β := β) L) := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    change v115WordSubstitution φ w ∈ L at hw
    refine
      ⟨v115InverseEncoding φ w, ?_, ?_⟩
    · constructor
      · exact ⟨w, rfl⟩
      · change
          v115WordSubstitution
            (v115IntermediateErase (α := α) (β := β))
            (v115InverseEncoding φ w) ∈ L
        rw [v115IntermediateErase_encoding]
        exact hw
    · exact v115IntermediateProject_encoding φ w
  · rintro ⟨v, ⟨henc, herase⟩, hproj⟩
    rcases henc with ⟨x, hx⟩
    subst v
    have hxw : x = w := by
      rw [v115IntermediateProject_encoding] at hproj
      exact hproj
    change v115WordSubstitution φ w ∈ L
    rw [← hxw]
    change
      v115WordSubstitution
        (v115IntermediateErase (α := α) (β := β))
        (v115InverseEncoding φ x) ∈ L
      at herase
    simpa only [v115IntermediateErase_encoding] using herase

end V115InverseHomReduction

end TCS1
end LeanCfgProject
