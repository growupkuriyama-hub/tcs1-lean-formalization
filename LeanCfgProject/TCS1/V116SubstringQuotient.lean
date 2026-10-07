import LeanCfgProject.TCS1.ReconstructionSoundness

/-!
# TCS #1 v116/v117: eliminate occurrence/context indices

The v115 reconstruction uses observed triples (factor, left, right).
The v116/v117 paper instead uses one nonterminal per nonempty observed
substring. Here the new derivation predicate is defined literally by the
(B)/(U)/(L) rules and proved equivalent, for every finite sample and every
fixed typing, to the already verified old R1--R4 semantics.

The result is exact *language* equality at every sample, not merely
agreement after characteristic data. The separate epsilon start is preserved.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V116SubstringQuotient

variable {α : Type u} {M : Type v} [Monoid M] [Fintype M]

/-- The non-start v116 derivation relation: one state for each word factor. -/
inductive V116FactorDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Word α → Word α → Prop
  | lexical {a : α}
      (hobs : ∃ u v, Observed K [a] u v) :
      V116FactorDerives H K [a] [a]
  | unary {x y w : Word α}
      (hshared : ∃ u v, Observed K x u v ∧ Observed K y u v)
      (htype : H.h x = H.h y)
      (d : V116FactorDerives H K y w) :
      V116FactorDerives H K x w
  | binary {x y w₁ w₂ : Word α}
      (hobs : ∃ u v, Observed K (x ++ y) u v)
      (hx : x ≠ []) (hy : y ≠ [])
      (dl : V116FactorDerives H K x w₁)
      (dr : V116FactorDerives H K y w₂) :
      V116FactorDerives H K (x ++ y) (w₁ ++ w₂)

/-- Collapse each old occurrence state to its factor; R2 becomes zero steps. -/
theorem v116_old_to_new
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    V116FactorDerives H K x w := by
  induction d with
  | @r4 a u v hobs =>
      exact V116FactorDerives.lexical ⟨u, v, hobs⟩
  | @r3 x y u v w hobs hobs' htype d ih =>
      exact V116FactorDerives.unary
        ⟨u, v, hobs, hobs'⟩ htype ih
  | @r2 x u v u' v' w hobs hobs' d ih =>
      exact ih
  | @r1 x y u v w₁ w₂ hparent hleft hright dl dr ihl ihr =>
      exact V116FactorDerives.binary
        ⟨u, v, hparent⟩ hleft.1 hright.1 ihl ihr

/--
A v116 derivation can be simulated starting from *any* observed old
representative. R2 first transports to a context witnessing the next rule.
-/
theorem v116_new_to_old
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x w : Word α}
    (d : V116FactorDerives H K x w) :
    ∀ u v, Observed K x u v → HypDerives H K x u v w := by
  induction d with
  | @lexical a hobs =>
      intro u v hcurrent
      exact HypDerives.r4 hcurrent
  | @unary x y w hshared htype dy ih =>
      intro u v hcurrent
      rcases hshared with ⟨p, q, hx, hy⟩
      exact HypDerives.r2 hcurrent hx
        (HypDerives.r3 hx hy htype (ih p q hy))
  | @binary x y w₁ w₂ hobs hx hy dl dr ihl ihr =>
      intro u v hcurrent
      rcases hobs with ⟨p, q, hparent⟩
      have hleft : Observed K x p (y ++ q) := by
        constructor
        · exact hx
        · simpa only [List.append_assoc] using hparent.2
      have hright : Observed K y (p ++ x) q := by
        constructor
        · exact hy
        · simpa only [List.append_assoc] using hparent.2
      exact HypDerives.r2 hcurrent hparent
        (HypDerives.r1 hparent hleft hright
          (ihl p (y ++ q) hleft) (ihr (p ++ x) q hright))

/-- v116 start rule: enter each nonempty observed sample, or emit epsilon. -/
inductive V116BatchDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Word α → Prop
  | nonempty {s w : Word α}
      (hs : s ∈ K) (hs_ne : s ≠ [])
      (d : V116FactorDerives H K s w) :
      V116BatchDerives H K w
  | epsilon (heps : ([] : Word α) ∈ K) :
      V116BatchDerives H K []

/-- Extensional language of the new substring-indexed grammar. -/
def V116BatchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) : Set (Word α) :=
  {w | V116BatchDerives H K w}

/-- Exact equivalence of the old and new batch constructors for ALL finite K. -/
theorem v116_batchLanguage_eq_v115
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    V116BatchLanguage H K = BatchLanguage H K := by
  apply Set.ext
  intro w
  constructor
  · intro h
    change V116BatchDerives H K w at h
    cases h with
    | @nonempty s w hs hs_ne d =>
        exact BatchDerives.nonempty hs hs_ne
          (v116_new_to_old H K d [] []
            ⟨hs_ne, by simpa using hs⟩)
    | epsilon heps =>
        exact BatchDerives.epsilon heps
  · intro h
    change BatchDerives H K w at h
    cases h with
    | @nonempty s w hs hs_ne d =>
        exact V116BatchDerives.nonempty
          hs hs_ne (v116_old_to_new H K d)
    | epsilon heps =>
        exact V116BatchDerives.epsilon heps


/-- Manuscript v116: the substring-indexed constructor is sample-consistent. -/
theorem v116_sample_consistency
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    (↑K : Set (Word α)) ⊆ V116BatchLanguage H K := by
  rw [v116_batchLanguage_eq_v115 H K]
  exact sample_consistency H K

/-- Manuscript v116: soundness transfers without a separate new induction. -/
theorem v116_batchLanguage_sound
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (L : Set (Word α))
    (hK : (↑K : Set (Word α)) ⊆ L)
    (hsub : FixedHSubstitutable H L) :
    V116BatchLanguage H K ⊆ L := by
  rw [v116_batchLanguage_eq_v115 H K]
  exact batchLanguage_sound H K L hK hsub

/--
The exact Gold-style characteristic-sample condition transfers in BOTH
directions, uniformly for every finite positive extension K of C.
-/
theorem v116_characteristic_sample_iff
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (C : Finset (Word α)) :
    (∀ K : Finset (Word α),
      C ⊆ K →
      (↑K : Set (Word α)) ⊆ L →
      V116BatchLanguage H K = L) ↔
    (∀ K : Finset (Word α),
      C ⊆ K →
      (↑K : Set (Word α)) ⊆ L →
      BatchLanguage H K = L) := by
  constructor
  · intro h K hC hpos
    rw [← v116_batchLanguage_eq_v115 H K]
    exact h K hC hpos
  · intro h K hC hpos
    rw [v116_batchLanguage_eq_v115 H K]
    exact h K hC hpos

end V116SubstringQuotient

end TCS1
end LeanCfgProject
