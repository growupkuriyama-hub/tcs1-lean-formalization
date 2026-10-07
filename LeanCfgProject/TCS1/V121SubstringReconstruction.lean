import LeanCfgProject.TCS1.ReconstructionSoundness

/-!
# TCS #1 v121: substring-indexed reconstruction

The v116--v121 manuscript replaces occurrence/context-indexed hypothesis
states `[x;u,v]` by one state `[x]` for each observed nonempty factor.
This file formalizes the exact quotient at the derivation-tree level.

The key result is extensional: for every finite sample and fixed typing, the
substring-indexed batch language is exactly the already-verified
occurrence-indexed `BatchLanguage`.  Consequently the existing soundness,
finite-witness completeness, conservative Gold convergence, and executable
bridges can be reused without changing their language-level conclusions.

No `sorry`, `admit`, or project-level axiom is used.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V121SubstringReconstruction

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- A nonempty factor occurs somewhere in the finite positive sample. -/
def SubstringObserved
    (K : Finset (Word α))
    (x : Word α) : Prop :=
  ∃ u v : Word α, Observed K x u v

theorem substringObserved_of_observed
    {K : Finset (Word α)}
    {x u v : Word α}
    (h : Observed K x u v) :
    SubstringObserved K x :=
  ⟨u, v, h⟩

/--
Derivation semantics of the v116--v121 substring-indexed rules (L), (U), (B).

* `lexical` is Rule (L);
* `unary` is Rule (U), with an explicit common observed context;
* `binary` is Rule (B).

The start rule is packaged separately below.
-/
inductive SubstringDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Word α → Word α → Prop
  | lexical
      {a : α}
      (hobs : SubstringObserved K [a]) :
      SubstringDerives H K [a] [a]
  | unary
      {x y w : Word α}
      (hshared :
        ∃ u v : Word α,
          Observed K x u v ∧
          Observed K y u v)
      (htype : H.h x = H.h y)
      (d : SubstringDerives H K y w) :
      SubstringDerives H K x w
  | binary
      {x y w₁ w₂ : Word α}
      (hx : x ≠ [])
      (hy : y ≠ [])
      (hparent : SubstringObserved K (x ++ y))
      (dleft : SubstringDerives H K x w₁)
      (dright : SubstringDerives H K y w₂) :
      SubstringDerives H K (x ++ y) (w₁ ++ w₂)

/-- Every substring-indexed derivation produces a nonempty word. -/
theorem substringDerives_nonempty
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x w : Word α}
    (d : SubstringDerives H K x w) :
    w ≠ [] := by
  induction d with
  | lexical hobs =>
      simp
  | unary hshared htype d ih =>
      exact ih
  | binary hx hy hparent dleft dright ihleft ihrigh =>
      exact append_ne_nil_of_left_ne_nil ihleft

/--
Every old occurrence-indexed derivation maps to a v121 substring-indexed
derivation.  Old context transport (R2) becomes zero steps.
-/
theorem hypDerives_to_substringDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    SubstringDerives H K x w := by
  induction d with
  | @r4 a u v hobs =>
      exact SubstringDerives.lexical
        (substringObserved_of_observed hobs)
  | @r3 x x' u v w hobs hobs' htype d ih =>
      exact SubstringDerives.unary
        ⟨u, v, hobs, hobs'⟩ htype ih
  | @r2 x u v u' v' w hobs hobs' d ih =>
      exact ih
  | @r1 x y u v w₁ w₂ hparent hleft hright dleft dright ihleft ihrigh =>
      exact SubstringDerives.binary
        hleft.1 hright.1
        (substringObserved_of_observed hparent)
        ihleft ihrigh

/--
A v121 derivation rooted at `[x]` can be simulated from any old
occurrence-indexed representative `[x;u,v]`.
-/
theorem substringDerives_to_hypDerives_at
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x w : Word α}
    (d : SubstringDerives H K x w) :
    ∀ {u v : Word α},
      Observed K x u v →
      HypDerives H K x u v w := by
  induction d with
  | @lexical a hfactor =>
      intro u v hobs
      exact HypDerives.r4 hobs
  | @unary x y w hshared htype d ih =>
      intro u v hobs
      rcases hshared with ⟨p, q, hxpq, hypq⟩
      have dy : HypDerives H K y p q w :=
        ih hypq
      have dxpq : HypDerives H K x p q w :=
        HypDerives.r3 hxpq hypq htype dy
      exact HypDerives.r2 hobs hxpq dxpq
  | @binary x y w₁ w₂ hx hy hparent dleft dright ihleft ihrigh =>
      intro u v hobs
      have hleft : Observed K x u (y ++ v) := by
        refine ⟨hx, ?_⟩
        simpa only [List.append_assoc] using hobs.2
      have hright : Observed K y (u ++ x) v := by
        refine ⟨hy, ?_⟩
        simpa only [List.append_assoc] using hobs.2
      exact
        HypDerives.r1
          hobs hleft hright
          (ihleft hleft)
          (ihright hright)

/-- Old and new non-start derivation semantics are extensionally equivalent
once an old representative occurrence is fixed. -/
theorem substringDerives_iff_hypDerives_at
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v w : Word α}
    (hobs : Observed K x u v) :
    SubstringDerives H K x w ↔
      HypDerives H K x u v w := by
  constructor
  · intro d
    exact substringDerives_to_hypDerives_at H K d hobs
  · intro d
    exact hypDerives_to_substringDerives H K d

/-- Start-rule semantics for the v121 substring-indexed reconstruction. -/
inductive SubstringBatchDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Word α → Prop
  | nonempty
      {s w : Word α}
      (hs : s ∈ K)
      (hs_ne : s ≠ [])
      (d : SubstringDerives H K s w) :
      SubstringBatchDerives H K w
  | epsilon
      (heps : ([] : Word α) ∈ K) :
      SubstringBatchDerives H K []

def SubstringBatchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Set (Word α) :=
  {w | SubstringBatchDerives H K w}

theorem batchDerives_to_substringBatchDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {w : Word α}
    (d : BatchDerives H K w) :
    SubstringBatchDerives H K w := by
  cases d with
  | nonempty hs hs_ne dh =>
      exact
        SubstringBatchDerives.nonempty
          hs hs_ne
          (hypDerives_to_substringDerives H K dh)
  | epsilon heps =>
      exact SubstringBatchDerives.epsilon heps

theorem substringBatchDerives_to_batchDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {w : Word α}
    (d : SubstringBatchDerives H K w) :
    BatchDerives H K w := by
  cases d with
  | @nonempty s w hs hs_ne ds =>
      have hobs : Observed K s [] [] := by
        refine ⟨hs_ne, ?_⟩
        simpa using hs
      exact
        BatchDerives.nonempty
          hs hs_ne
          (substringDerives_to_hypDerives_at H K ds hobs)
  | epsilon heps =>
      exact BatchDerives.epsilon heps

/-- Exact v115 -> v116/v121 quotient theorem at the generated-language level. -/
theorem substringBatchLanguage_eq_batchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    SubstringBatchLanguage H K =
      BatchLanguage H K := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    exact substringBatchDerives_to_batchDerives H K hw
  · intro hw
    exact batchDerives_to_substringBatchDerives H K hw

/-- Sample consistency transfers immediately to the current constructor. -/
theorem substring_sample_consistency
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    (↑K : Set (Word α)) ⊆
      SubstringBatchLanguage H K := by
  rw [substringBatchLanguage_eq_batchLanguage]
  exact sample_consistency H K

/-- Soundness transfers immediately to the current constructor. -/
theorem substring_batchLanguage_sound
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (L : Set (Word α))
    (hK : (↑K : Set (Word α)) ⊆ L)
    (hsub : FixedHSubstitutable H L) :
    SubstringBatchLanguage H K ⊆ L := by
  rw [substringBatchLanguage_eq_batchLanguage]
  exact batchLanguage_sound H K L hK hsub

end V121SubstringReconstruction

end TCS1
end LeanCfgProject
