import LeanCfgProject.TCS1.FixedWindowConcreteMonoid
import Mathlib.Tactic

/-!
# TCS #1 v126: reverse fixed-window kernel obstruction from non-local triviality

This module formalizes the reverse witness used in Proposition
"locally trivial typings and fixed windows".

For a finite typing H, define local triviality on its positive image inside the
ambient monoid.  If that property fails, there are positive-image elements
e,m with e idempotent and e*m*e != e.  Choose nonempty words r,z representing
them.  For each fixed window (k,l), repeat r sufficiently often on both sides:

  x = R r R,   y = R z R.

The common long prefix/suffix R makes x and y have the same h_{k,l} type,
while H(x)=e and H(y)=e*m*e are different.  Therefore no fixed-window kernel
can refine H on nonempty words.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V126NonLocalTrivialWindowObstruction

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Positive image h(Sigma+), represented as a predicate in the ambient
finite monoid. -/
def PositiveImage
    (H : FixedFiniteMonoidHom α M)
    (m : M) : Prop :=
  ∃ w : Word α, w ≠ [] ∧ H.h w = m

/-- Manuscript local-triviality condition restricted to the positive image. -/
def PositiveImageLocallyTrivial
    (H : FixedFiniteMonoidHom α M) : Prop :=
  ∀ e : M,
    PositiveImage H e →
    e * e = e →
    ∀ t : M,
      PositiveImage H t →
      e * t * e = e

/-- Repetition of a nonempty factor, avoiding any semigroup identity issue in
the word-level construction. -/
def wordRepeat
    (r : Word α) : Nat → Word α
  | 0 => []
  | n + 1 => wordRepeat r n ++ r

@[simp] theorem wordRepeat_length
    (r : Word α) (n : Nat) :
    (wordRepeat r n).length = n * r.length := by
  induction n with
  | zero => simp [wordRepeat]
  | succ n ih =>
      simp [wordRepeat, ih, Nat.succ_mul]

theorem wordRepeat_type
    (H : FixedFiniteMonoidHom α M)
    (r : Word α) (n : Nat) :
    H.h (wordRepeat r n) = (H.h r) ^ n := by
  induction n with
  | zero =>
      simp [wordRepeat, H.map_nil]
  | succ n ih =>
      rw [wordRepeat, H.map_append, ih, pow_succ]

/-- Every positive power of an idempotent equals the idempotent. -/
theorem pow_eq_self_of_idempotent
    {e : M}
    (he : e * e = e) :
    ∀ {n : Nat}, 0 < n → e ^ n = e := by
  intro n hn
  cases n with
  | zero => omega
  | succ n =>
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ]
          have ih' : e ^ (n + 1) = e := ih (by omega)
          rw [ih', he]

/-- A long repeated boundary word R makes R x R and R y indistinguishable by
the fixed (k,l) summary, for arbitrary middle factors x,y. -/
theorem repeated_boundary_same_fixedWindow
    [Fintype α]
    (k l : Nat)
    {R x y : Word α}
    (hR : max k l ≤ R.length)
    (hRne : R ≠ []) :
    (fixedWindowMonoidHom (α := α) k l).h (R ++ x ++ R) =
      (fixedWindowMonoidHom (α := α) k l).h (R ++ y ++ R) := by
  let p : Word α := R.take k
  let q : Word α := R.drop (R.length - l)
  have hk : k ≤ R.length := le_trans (Nat.le_max_left _ _) hR
  have hl : l ≤ R.length := le_trans (Nat.le_max_right _ _) hR
  have hp : p.length = k := by
    simp [p, List.length_take, hk]
  have hq : q.length = l := by
    simp [q, List.length_drop]
    omega
  have hpre : p ++ R.drop k = R := by
    simpa [p] using (List.take_append_drop k R)
  have hsuf :
      R.take (R.length - l) ++ q = R := by
    simpa [q] using
      (List.take_append_drop (R.length - l) R)
  let mx : Word α :=
    R.drop k ++ x ++ R.take (R.length - l)
  let my : Word α :=
    R.drop k ++ y ++ R.take (R.length - l)
  have hxshape :
      R ++ x ++ R = p ++ mx ++ q := by
    calc
      R ++ x ++ R
          = (p ++ R.drop k) ++ x ++
              (R.take (R.length - l) ++ q) := by
                rw [hpre, hsuf]
      _ = p ++ mx ++ q := by
            simp only [mx, List.append_assoc]
  have hyshape :
      R ++ y ++ R = p ++ my ++ q := by
    calc
      R ++ y ++ R
          = (p ++ R.drop k) ++ y ++
              (R.take (R.length - l) ++ q) := by
                rw [hpre, hsuf]
      _ = p ++ my ++ q := by
            simp only [my, List.append_assoc]
  have hsum :
      k + l ≤ (R ++ x ++ R).length := by
    simp only [List.length_append]
    omega
  have hsum' :
      k + l ≤ (R ++ y ++ R).length := by
    simp only [List.length_append]
    omega
  have hpos :
      0 < (R ++ x ++ R).length := by
    have : 0 < R.length := List.length_pos.mpr hRne
    simp only [List.length_append]
    omega
  have hpos' :
      0 < (R ++ y ++ R).length := by
    have : 0 < R.length := List.length_pos.mpr hRne
    simp only [List.length_append]
    omega
  have hcut :
      fixedWindowThreshold k l ≤
        (R ++ x ++ R).length := by
    unfold fixedWindowThreshold
    omega
  have hcut' :
      fixedWindowThreshold k l ≤
        (R ++ y ++ R).length := by
    unfold fixedWindowThreshold
    omega
  have hsame :
      SameFixedWindowSummary k l
        (R ++ x ++ R) (R ++ y ++ R) :=
    Or.inr
      ⟨hcut, hcut',
        p, q, mx, my,
        hp, hq,
        hxshape, hyshape⟩
  exact
    fixedWindowMonoidHom_respects
      (α := α) k l
      (R ++ x ++ R) (R ++ y ++ R) hsame

/-- Explicit counterexample form of failure of positive-image local triviality. -/
theorem exists_positive_local_trivial_counterexample
    (H : FixedFiniteMonoidHom α M)
    (hnot : ¬ PositiveImageLocallyTrivial H) :
    ∃ e m : M,
      PositiveImage H e ∧
      e * e = e ∧
      PositiveImage H m ∧
      e * m * e ≠ e := by
  classical
  unfold PositiveImageLocallyTrivial at hnot
  push_neg at hnot
  rcases hnot with ⟨e, hepos, heidem, m, hmpos, hbad⟩
  exact ⟨e, m, hepos, heidem, hmpos, hbad⟩

/-- Main reverse witness: if the positive image of H is not locally trivial,
then every fixed window collapses some nonempty pair that H separates. -/
theorem nonLocalTrivial_obstructs_every_fixedWindow
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (hnot : ¬ PositiveImageLocallyTrivial H)
    (k l : Nat) :
    ∃ x y : Word α,
      x ≠ [] ∧
      y ≠ [] ∧
      (fixedWindowMonoidHom (α := α) k l).h x =
        (fixedWindowMonoidHom (α := α) k l).h y
      ∧
      H.h x ≠ H.h y := by
  obtain ⟨e, m, hepos, heidem, hmpos, hbad⟩ :=
    exists_positive_local_trivial_counterexample H hnot
  rcases hepos with ⟨r, hrne, hr⟩
  rcases hmpos with ⟨z, hzne, hz⟩
  let j : Nat := max k l + 1
  let R : Word α := wordRepeat r j
  have hrlen : 0 < r.length := List.length_pos.mpr hrne
  have hjpos : 0 < j := by
    dsimp [j]
    omega
  have hRlen : R.length = j * r.length := by
    simp [R]
  have hRbound : max k l ≤ R.length := by
    rw [hRlen]
    dsimp [j]
    nlinarith
  have hRne : R ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [hRlen]
    exact Nat.mul_pos hjpos hrlen
  have hRtype : H.h R = e := by
    rw [show H.h R = (H.h r) ^ j by
      simpa [R] using wordRepeat_type H r j]
    rw [hr]
    exact pow_eq_self_of_idempotent heidem hjpos
  let x : Word α := R ++ r ++ R
  let y : Word α := R ++ z ++ R
  have hxne : x ≠ [] := by
    dsimp [x]
    exact append_ne_nil_of_left_ne_nil hRne
  have hyne : y ≠ [] := by
    dsimp [y]
    exact append_ne_nil_of_left_ne_nil hRne
  have hwindow :
      (fixedWindowMonoidHom (α := α) k l).h x =
        (fixedWindowMonoidHom (α := α) k l).h y := by
    dsimp [x, y]
    exact repeated_boundary_same_fixedWindow
      (α := α) k l hRbound hRne
  have hxH : H.h x = e := by
    dsimp [x]
    calc
      H.h (R ++ r ++ R)
          = H.h (R ++ r) * H.h R :=
            H.map_append (R ++ r) R
      _ = (H.h R * H.h r) * H.h R := by
            rw [H.map_append]
      _ = (e * e) * e := by rw [hRtype, hr]
      _ = e := by rw [heidem, heidem]
  have hyH : H.h y = e * m * e := by
    dsimp [y]
    calc
      H.h (R ++ z ++ R)
          = H.h (R ++ z) * H.h R :=
            H.map_append (R ++ z) R
      _ = (H.h R * H.h z) * H.h R := by
            rw [H.map_append]
      _ = e * m * e := by rw [hRtype, hz]
  refine ⟨x, y, hxne, hyne, hwindow, ?_⟩
  rw [hxH, hyH]
  exact hbad

end V126NonLocalTrivialWindowObstruction

end TCS1
end LeanCfgProject
