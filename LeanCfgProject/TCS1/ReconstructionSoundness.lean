import LeanCfgProject.TCS1.YieldTypedRefinementCore

/-!
# TCS #1 v63: reconstruction soundness

This file formalizes the proof kernel of Section 4 ("Finite-sample
reconstruction") and Theorem 4.2 ("soundness") of the current v63 manuscript.

Rather than introducing a second generic CFG library, the inductive predicate
`HypDerives H K x u v w` is the derivation-tree semantics of the four
non-start rules R1--R4 for the bracketed nonterminal `[x:u,v]`.

The theorem `hypDerives_soundnessInvariant` is the displayed simultaneous
invariant from the paper:

  [x:u,v] =>* w  ==>  u w v in L  and  h(w)=h(x).

The start rule R5 is then added by `BatchDerives`, yielding the full
reconstruction soundness theorem.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section Reconstruction

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- A bracketed hypothesis nonterminal is available exactly when its internal
factor is nonempty and the displayed occurrence is observed in the sample. -/
def Observed
    (K : Finset (Word α))
    (x u v : Word α) : Prop :=
  x ≠ [] ∧ u ++ x ++ v ∈ K

/--
Derivation-tree semantics of the reconstruction rules R1--R4.
The arguments `x u v w` represent `[x:u,v] =>* w`.
-/
inductive HypDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Word α → Word α → Word α → Word α → Prop
  | r4
      {a : α} {u v : Word α}
      (hobs : Observed K [a] u v) :
      HypDerives H K [a] u v [a]
  | r3
      {x x' u v w : Word α}
      (hobs : Observed K x u v)
      (hobs' : Observed K x' u v)
      (htype : H.h x = H.h x')
      (d : HypDerives H K x' u v w) :
      HypDerives H K x u v w
  | r2
      {x u v u' v' w : Word α}
      (hobs : Observed K x u v)
      (hobs' : Observed K x u' v')
      (d : HypDerives H K x u' v' w) :
      HypDerives H K x u v w
  | r1
      {x y u v w₁ w₂ : Word α}
      (hparent : Observed K (x ++ y) u v)
      (hleft : Observed K x u (y ++ v))
      (hright : Observed K y (u ++ x) v)
      (dleft : HypDerives H K x u (y ++ v) w₁)
      (dright : HypDerives H K y (u ++ x) v w₂) :
      HypDerives H K (x ++ y) u v (w₁ ++ w₂)

/-- Appending anything to a nonempty word keeps it nonempty. -/
theorem append_ne_nil_of_left_ne_nil
    {a b : Word α}
    (ha : a ≠ []) :
    a ++ b ≠ [] := by
  cases a with
  | nil => contradiction
  | cons x xs => simp

/-- R1--R4 contain no erasing derivation. -/
theorem hypDerives_nonempty
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    w ≠ [] := by
  induction d with
  | r4 _hobs =>
      simp
  | r3 _hobs _hobs' _htype _d ih =>
      exact ih
  | r2 _hobs _hobs' _d ih =>
      exact ih
  | r1 _hparent _hleft _hright _dleft _dright ihleft _ihright =>
      exact append_ne_nil_of_left_ne_nil ihleft

/--
Every observed factor derives itself using only R1 and R4.
This is the derivation-tree core of sample consistency.
-/
theorem observed_self_derives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v : Word α}
    (hobs : Observed K x u v) :
    HypDerives H K x u v x := by
  induction x generalizing u v with
  | nil =>
      exact False.elim (hobs.1 rfl)
  | cons a xs ih =>
      cases xs with
      | nil =>
          exact HypDerives.r4 hobs
      | cons b bs =>
          let y : Word α := b :: bs
          have hy_ne : y ≠ [] := by simp [y]
          have hparent : Observed K ([a] ++ y) u v := by
            simpa [y] using hobs
          have hleft : Observed K [a] u (y ++ v) := by
            constructor
            · simp
            · simpa [y, List.append_assoc] using hobs.2
          have hright : Observed K y (u ++ [a]) v := by
            constructor
            · exact hy_ne
            · simpa [y, List.append_assoc] using hobs.2
          have dleft : HypDerives H K [a] u (y ++ v) [a] :=
            HypDerives.r4 hleft
          have dright : HypDerives H K y (u ++ [a]) v y := by
            apply ih
            exact hright
          have d :=
            HypDerives.r1
              (H := H) (K := K)
              hparent hleft hright dleft dright
          simpa [y] using d

/--
The simultaneous soundness invariant displayed in the v63 manuscript.
-/
theorem hypDerives_soundnessInvariant
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (L : Set (Word α))
    (hK : (↑K : Set (Word α)) ⊆ L)
    (hsub : FixedHSubstitutable H L)
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    u ++ w ++ v ∈ L ∧ H.h w = H.h x := by
  induction d with
  | @r4 a u v hobs =>
      constructor
      · exact hK hobs.2
      · rfl

  | @r3 x x' u v w hobs hobs' htype d ih =>
      constructor
      · exact ih.1
      · calc
          H.h w = H.h x' := ih.2
          _ = H.h x := htype.symm

  | @r2 x u v u' v' w hobs hobs' d ih =>
      have hw_ne : w ≠ [] :=
        hypDerives_nonempty H K d
      have hxL' : u' ++ x ++ v' ∈ L :=
        hK hobs'.2
      have hshared : HaveSharedContext L x w := by
        exact ⟨u', v', hxL', ih.1⟩
      have hdist : Distribution L x = Distribution L w :=
        hsub hobs.1 hw_ne ih.2.symm hshared
      have hctx_x : (u, v) ∈ Distribution L x := by
        exact hK hobs.2
      have hctx_w : (u, v) ∈ Distribution L w := by
        rw [← hdist]
        exact hctx_x
      constructor
      · exact hctx_w
      · exact ih.2

  | @r1 x y u v w₁ w₂ hparent hleft hright dleft dright ihleft ihrigh =>
      have hw₁_ne : w₁ ≠ [] :=
        hypDerives_nonempty H K dleft
      have hxyL : u ++ x ++ (y ++ v) ∈ L := by
        simpa only [List.append_assoc] using hK hparent.2
      have hshared : HaveSharedContext L x w₁ := by
        exact ⟨u, y ++ v, hxyL, ihleft.1⟩
      have hdist : Distribution L x = Distribution L w₁ :=
        hsub hleft.1 hw₁_ne ihleft.2.symm hshared
      have hctx_x : (u, w₂ ++ v) ∈ Distribution L x := by
        change u ++ x ++ (w₂ ++ v) ∈ L
        simpa only [List.append_assoc] using ihrigh.1
      have hctx_w₁ : (u, w₂ ++ v) ∈ Distribution L w₁ := by
        rw [← hdist]
        exact hctx_x
      constructor
      · have hmem : u ++ w₁ ++ (w₂ ++ v) ∈ L := by
          change u ++ w₁ ++ (w₂ ++ v) ∈ L at hctx_w₁
          exact hctx_w₁
        simpa only [List.append_assoc] using hmem
      · calc
          H.h (w₁ ++ w₂) = H.h w₁ * H.h w₂ :=
            H.map_append w₁ w₂
          _ = H.h x * H.h y := by rw [ihleft.2, ihrigh.2]
          _ = H.h (x ++ y) := (H.map_append x y).symm

/-- Start-rule semantics R5, including the separate epsilon start rule. -/
inductive BatchDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Word α → Prop
  | nonempty
      {s w : Word α}
      (hs : s ∈ K)
      (hs_ne : s ≠ [])
      (d : HypDerives H K s [] [] w) :
      BatchDerives H K w
  | epsilon
      (heps : ([] : Word α) ∈ K) :
      BatchDerives H K []

/-- Language generated by the set-driven reconstruction operator. -/
def BatchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    Set (Word α) :=
  { w | BatchDerives H K w }

/-- Lemma 4.1 (sample consistency) at the derivation-tree level. -/
theorem sample_consistency
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    (↑K : Set (Word α)) ⊆ BatchLanguage H K := by
  intro w hw
  by_cases hw_nil : w = []
  · subst w
    exact BatchDerives.epsilon hw
  · exact BatchDerives.nonempty
      hw hw_nil
      (observed_self_derives H K ⟨hw_nil, by simpa using hw⟩)

/--
Theorem 4.2 (soundness): every word generated by the reconstruction operator
belongs to the positive target whenever the sample is positive and the target
is fixed-h substitutable.
-/
theorem batchLanguage_sound
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (L : Set (Word α))
    (hK : (↑K : Set (Word α)) ⊆ L)
    (hsub : FixedHSubstitutable H L) :
    BatchLanguage H K ⊆ L := by
  intro w hw
  cases hw with
  | nonempty hs hs_ne d =>
      have hinv :=
        hypDerives_soundnessInvariant H K L hK hsub d
      simpa using hinv.1
  | epsilon heps =>
      exact hK heps

end Reconstruction

end TCS1
end LeanCfgProject
