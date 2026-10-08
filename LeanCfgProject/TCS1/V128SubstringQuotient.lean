import LeanCfgProject.TCS1.ReconstructionSoundness

/-!
# TCS #1 v128: exact v115/v116 reconstruction quotient

The v115 hypothesis uses observed occurrence states (x,u,v), represented by
`HypDerives`; the v116 hypothesis uses one state per observed *factor* x.
The inductive `SubstringDerives` below gives exact semantics to v116 rules
L (letter), U (shared-context typed unary), and B (binary split).

Both simulations are proved for arbitrary finite positive samples K and
arbitrary fixed finite-monoid typings H. In particular, the reverse
simulation works from *every* observed occurrence of the root factor.
The separate epsilon start rule is preserved exactly.

This is an extensional start-language theorem; a subsequent bridge should
connect this inductive semantics to an explicitly materialized finite CFG
with exactly the manuscript's v116 productions and size bounds.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section Quotient

variable {α : Type u} {M : Type v}
variable [Monoid M] [Fintype M]

/-- Rule U: two nonempty sample factors share one observed context and h-type. -/
def SubstringUnaryRelated
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (x y : Word α) : Prop :=
  H.h x = H.h y ∧
    ∃ p q : Word α, Observed K x p q ∧ Observed K y p q

/-- v116 non-start derivations with one nonterminal per observed factor. -/
inductive SubstringDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Word α → Word α → Prop
  | letter {a : α}
      (hobs : ∃ p q : Word α, Observed K [a] p q) :
      SubstringDerives H K [a] [a]
  | unary {x y w : Word α}
      (hrel : SubstringUnaryRelated H K x y)
      (d : SubstringDerives H K y w) :
      SubstringDerives H K x w
  | binary {x y w₁ w₂ : Word α}
      (hparent : ∃ p q : Word α, Observed K (x ++ y) p q)
      (hx : x ≠ [])
      (hy : y ≠ [])
      (dx : SubstringDerives H K x w₁)
      (dy : SubstringDerives H K y w₂) :
      SubstringDerives H K (x ++ y) (w₁ ++ w₂)

/-- Erasing occurrence contexts simulates every v115 derivation in v116. -/
theorem hypDerives_to_substringDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    SubstringDerives H K x w := by
  induction d with
  | r4 hobs =>
      exact SubstringDerives.letter ⟨_, _, hobs⟩
  | r3 hobs hobs' htype _d ih =>
      exact SubstringDerives.unary ⟨htype, ⟨_, _, hobs, hobs'⟩⟩ ih
  | r2 _hobs _hobs' _d ih =>
      exact ih
  | r1 hparent hleft hright _dl _dr ihl ihr =>
      exact SubstringDerives.binary
        ⟨_, _, hparent⟩ hleft.1 hright.1 ihl ihr

/-- Every v116 derivation is reproducible from *any* v115 occurrence. -/
theorem substringDerives_to_hypDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x w : Word α}
    (d : SubstringDerives H K x w) :
    ∀ u v : Word α, Observed K x u v → HypDerives H K x u v w := by
  induction d with
  | letter _hobs =>
      intro u v hcurrent
      exact HypDerives.r4 hcurrent
  | @unary x y w hrel _dy ih =>
      intro u v hcurrent
      rcases hrel with ⟨htype, p, q, hxp, hyp⟩
      exact HypDerives.r2 hcurrent hxp
        (HypDerives.r3 hxp hyp htype (ih p q hyp))
  | @binary x y w₁ w₂ hparent hx hy _dx _dy ihl ihr =>
      intro u v hcurrent
      rcases hparent with ⟨p, q, hp⟩
      have hleft : Observed K x p (y ++ q) := by
        constructor
        · exact hx
        · simpa only [List.append_assoc] using hp.2
      have hright : Observed K y (p ++ x) q := by
        constructor
        · exact hy
        · simpa only [List.append_assoc] using hp.2
      exact HypDerives.r2 hcurrent hp
        (HypDerives.r1 hp hleft hright
          (ihl p (y ++ q) hleft)
          (ihr (p ++ x) q hright))

/-- v116 reconstructed start language, including the isolated epsilon rule. -/
def SubstringBatchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Set (Word α) :=
  {w | (∃ s : Word α, s ∈ K ∧ s ≠ [] ∧ SubstringDerives H K s w) ∨
    (w = [] ∧ ([] : Word α) ∈ K)}

/-- Exact v115/v116 language equality for every sample, including K = ∅. -/
theorem substringBatchLanguage_eq_batchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    SubstringBatchLanguage H K = BatchLanguage H K := by
  ext w
  change ((∃ s : Word α, s ∈ K ∧ s ≠ [] ∧ SubstringDerives H K s w) ∨
      (w = [] ∧ ([] : Word α) ∈ K)) ↔ BatchDerives H K w
  constructor
  · rintro (⟨s, hs, hsne, hd⟩ | ⟨rfl, heps⟩)
    · exact BatchDerives.nonempty hs hsne
        (substringDerives_to_hypDerives H K hd [] [] ⟨hsne, by simpa using hs⟩)
    · exact BatchDerives.epsilon heps
  · intro hd
    cases hd with
    | nonempty hs hsne d =>
        exact Or.inl ⟨_, hs, hsne, hypDerives_to_substringDerives H K d⟩
    | epsilon heps =>
        exact Or.inr ⟨rfl, heps⟩

end Quotient

end TCS1
end LeanCfgProject
