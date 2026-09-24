import LeanCfgProject.TCS1.FixedHSubstitutability
import Mathlib.Computability.DFA

/-!
# TCS #1 v79: regular languages and finite-monoid recognition

This module closes the background Proposition 3.1 interface used by the
manuscript.  Mathlib defines regular languages by finite DFAs.  We connect
that definition explicitly to the paper's finite-monoid observation model.

For a finite DFA, the recognizing monoid is its full transition monoid.
Conversely, a finite-monoid homomorphism with an accepting subset gives the
usual Cayley-style DFA on the monoid itself.

Together with `recognizedPreimage_fixedHSubstitutable`, this verifies the
paper-facing statement that every regular language is a finite-monoid
preimage and every such preimage is fixed-h substitutable.
-/

namespace LeanCfgProject
namespace TCS1

universe u

/-- Wrapper for the full transformation monoid of a finite DFA state set. -/
structure DFATransition (σ : Type) where
  toFun : σ → σ

@[ext] theorem DFATransition.ext
    {σ : Type}
    {f g : DFATransition σ}
    (h : ∀ q, f.toFun q = g.toFun q) :
    f = g := by
  cases f
  cases g
  congr
  funext q
  exact h q

instance {σ : Type} : One (DFATransition σ) where
  one := ⟨id⟩

/--
Multiplication follows input order: `f * g` first performs `f`, then
`g`.  Thus the word map satisfies h(uv)=h(u)h(v).
-/
instance {σ : Type} : Mul (DFATransition σ) where
  mul f g := ⟨fun q => g.toFun (f.toFun q)⟩

instance {σ : Type} : Monoid (DFATransition σ) where
  one_mul f := by
    ext q
    rfl
  mul_one f := by
    ext q
    rfl
  mul_assoc f g h := by
    ext q
    rfl

noncomputable instance {σ : Type} [Fintype σ] :
    Fintype (DFATransition σ) := by
  classical
  exact
    Fintype.ofEquiv (σ → σ)
      { toFun := fun f => ⟨f⟩
        invFun := fun t => t.toFun
        left_inv := by intro f; rfl
        right_inv := by intro t; cases t; rfl }

/-- The transition transformation induced by a word. -/
def dfaTransitionHom
    {α : Type u} {σ : Type}
    [Fintype σ]
    (D : DFA α σ) :
    FixedFiniteMonoidHom α (DFATransition σ) where
  h w := ⟨fun q => D.evalFrom q w⟩
  map_nil := by
    ext q
    rfl
  map_append u v := by
    ext q
    change
      D.evalFrom q (u ++ v) =
        D.evalFrom (D.evalFrom q u) v
    rw [DFA.evalFrom_of_append]

/-- Accepting transformations are those sending the start state to an accept state. -/
def dfaTransitionAccept
    {α : Type u} {σ : Type}
    [Fintype σ]
    (D : DFA α σ) :
    Set (DFATransition σ) :=
  {t | t.toFun D.start ∈ D.accept}

/-- The transition-monoid preimage is exactly the DFA language. -/
theorem dfa_recognizedPreimage_eq_accepts
    {α : Type u} {σ : Type}
    [Fintype σ]
    (D : DFA α σ) :
    RecognizedPreimage
        (dfaTransitionHom D)
        (dfaTransitionAccept D)
      =
    D.accepts := by
  apply Set.ext
  intro w
  rfl

/--
Every regular language has a finite-monoid recognition of the form used in
Proposition 3.1.
-/
theorem isRegular_exists_finiteMonoidRecognition
    {α : Type u}
    (L : Language α)
    (hreg : L.IsRegular) :
    ∃ σ : Type,
      ∃ _inst : Fintype σ,
        ∃ H : FixedFiniteMonoidHom α (DFATransition σ),
          ∃ Acc : Set (DFATransition σ),
            RecognizedPreimage H Acc = L := by
  rcases hreg with ⟨σ, hfin, D, hD⟩
  refine ⟨σ, hfin, dfaTransitionHom D,
    dfaTransitionAccept D, ?_⟩
  rw [dfa_recognizedPreimage_eq_accepts D]
  exact hD

/-- DFA associated with a finite-monoid recognition. -/
def monoidRecognitionDFA
    {α : Type u} {M : Type}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    (Acc : Set M) :
    DFA α M where
  step q a := q * H.h [a]
  start := 1
  accept := Acc

/-- Reading a word from state q multiplies q by its h-image. -/
theorem monoidRecognitionDFA_evalFrom
    {α : Type u} {M : Type}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    (Acc : Set M)
    (q : M)
    (w : Word α) :
    (monoidRecognitionDFA H Acc).evalFrom q w =
      q * H.h w := by
  induction w generalizing q with
  | nil =>
      simp [H.map_nil]
  | cons a w ih =>
      rw [DFA.evalFrom_cons]
      change
        (monoidRecognitionDFA H Acc).evalFrom
            (q * H.h [a]) w =
          q * H.h (a :: w)
      rw [ih]
      rw [show a :: w = [a] ++ w by rfl,
        H.map_append]
      simp [mul_assoc]

/-- The Cayley-style DFA recognizes exactly the finite-monoid preimage. -/
theorem monoidRecognitionDFA_accepts_eq
    {α : Type u} {M : Type}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    (Acc : Set M) :
    (monoidRecognitionDFA H Acc).accepts =
      RecognizedPreimage H Acc := by
  apply Set.ext
  intro w
  change
    (monoidRecognitionDFA H Acc).eval w ∈ Acc ↔
      H.h w ∈ Acc
  change
    (monoidRecognitionDFA H Acc).evalFrom 1 w ∈ Acc ↔
      H.h w ∈ Acc
  rw [monoidRecognitionDFA_evalFrom]
  simp

/-- Every finite-monoid preimage over a small finite monoid is regular. -/
theorem recognizedPreimage_isRegular
    {α : Type u}
    {M : Type}
    [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom α M)
    (Acc : Set M) :
    Language.IsRegular (RecognizedPreimage H Acc) := by
  refine ⟨M, inferInstance,
    monoidRecognitionDFA (α := α) (M := M) H Acc, ?_⟩
  exact
    monoidRecognitionDFA_accepts_eq
      (α := α) (M := M) H Acc

/--
Paper-facing finite-automaton / finite-monoid equivalence, split into the two
directions in a form that keeps all typeclass witnesses explicit.

The forward direction produces the full finite transition monoid of a DFA.
The converse accepts an arbitrary small finite monoid recognition.
-/
theorem regular_has_finiteMonoidRecognition
    {α : Type u}
    (L : Language α) :
    L.IsRegular →
      ∃ σ : Type,
        ∃ _inst : Fintype σ,
          ∃ D : DFA α σ,
            D.accepts = L ∧
            RecognizedPreimage
                (dfaTransitionHom D)
                (dfaTransitionAccept D)
              =
            L := by
  intro hreg
  rcases hreg with ⟨σ, hfin, D, hD⟩
  refine ⟨σ, hfin, D, hD, ?_⟩
  rw [dfa_recognizedPreimage_eq_accepts D]
  exact hD

/--
Every regular language belongs to at least one fixed-h substitutable class.

This is the paper-facing existential form used in the discussion of the union
class RS = ⋃_h RS_h: a finite DFA supplies its transition-monoid typing.
-/
theorem regular_exists_fixedHSubstitutable
    {α : Type u}
    (L : Language α)
    (hreg : L.IsRegular) :
    ∃ σ : Type,
      ∃ _inst : Fintype σ,
        ∃ D : DFA α σ,
          D.accepts = L ∧
          FixedHSubstitutable
            (dfaTransitionHom D) L := by
  rcases hreg with ⟨σ, hfin, D, hD⟩
  refine ⟨σ, hfin, D, hD, ?_⟩
  have hsub :=
    recognizedPreimage_fixedHSubstitutable
      (dfaTransitionHom D)
      (dfaTransitionAccept D)
  rw [dfa_recognizedPreimage_eq_accepts D, hD] at hsub
  exact hsub

/--
Complete Proposition 3.1 package.

1. Every regular language has an explicit finite transition-monoid
   recognition.
2. Every finite-monoid preimage is regular.
3. Every such preimage is fixed-h substitutable.
-/
theorem regular_auto_proposition_package
    {α : Type u}
    (L : Language α) :
    (L.IsRegular →
      ∃ σ : Type,
        ∃ _inst : Fintype σ,
          ∃ D : DFA α σ,
            D.accepts = L ∧
            RecognizedPreimage
                (dfaTransitionHom D)
                (dfaTransitionAccept D)
              =
            L)
    ∧
    (∀ (M : Type) [Monoid M] [Fintype M]
        (H : FixedFiniteMonoidHom α M)
        (Acc : Set M),
      Language.IsRegular (RecognizedPreimage H Acc))
    ∧
    (∀ (M : Type) [Monoid M] [Fintype M]
        (H : FixedFiniteMonoidHom α M)
        (Acc : Set M),
      FixedHSubstitutable H
        (RecognizedPreimage H Acc)) := by
  refine ⟨regular_has_finiteMonoidRecognition L, ?_, ?_⟩
  · intro M hmon hfin H Acc
    exact recognizedPreimage_isRegular H Acc
  · intro M hmon hfin H Acc
    exact recognizedPreimage_fixedHSubstitutable H Acc

end TCS1
end LeanCfgProject
