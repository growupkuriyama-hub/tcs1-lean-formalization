import LeanCfgProject.TCS1.FixedWindowConcreteMonoid

/-!
# TCS #1 v115: locally-trivial / fixed-window bridge, reverse direction

This module begins the machine proof of the new v115 Proposition 3.5.

It isolates the positive image semigroup of a fixed typing at the level needed
by the manuscript and proves the converse implication used in the algebraic
characterization:

  if some fixed-window kernel refines the nonempty kernel of h,
  then the positive image h(Sigma+) is locally trivial.

As a corollary, the positive image semigroup of every concrete fixed-window
typing h_{k,l} is locally trivial.

The forward implication (locally trivial positive image => the n,n window
kernel refines h, with n = |h(Sigma+)|) is proved separately, using the
finite-semigroup argument, in V115PositiveImageCardinal.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V115LocallyTrivialWindows

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Membership in the positive image h(Sigma+). -/
def V115InPositiveImage
    (H : FixedFiniteMonoidHom α M)
    (m : M) : Prop :=
  ∃ w : Word α, w ≠ [] ∧ H.h w = m

/--
Locally-trivial law on the positive image semigroup h(Sigma+).
Only positive-image elements are quantified, matching the manuscript's
S := h(Sigma+).
-/
def V115PositiveImageLocallyTrivial
    (H : FixedFiniteMonoidHom α M) : Prop :=
  ∀ e t : M,
    V115InPositiveImage H e →
    V115InPositiveImage H t →
    e * e = e →
    e * t * e = e

/-- Nonempty-kernel refinement between two fixed typings. -/
def V115NonemptyKernelRefines
    {N : Type w} [Monoid N] [Fintype N]
    (Hfine : FixedFiniteMonoidHom α N)
    (Hcoarse : FixedFiniteMonoidHom α M) : Prop :=
  ∀ x y : Word α,
    x ≠ [] →
    y ≠ [] →
    Hfine.h x = Hfine.h y →
    Hcoarse.h x = Hcoarse.h y

/-- Word repetition by concatenation, kept explicit for the finite-window witness. -/
def v115WordRepeat
    (w : Word α) : Nat → Word α
  | 0 => []
  | n + 1 => v115WordRepeat w n ++ w

@[simp] theorem v115WordRepeat_length
    (w : Word α) :
    ∀ n : Nat,
      (v115WordRepeat w n).length = n * w.length
  | 0 => by simp [v115WordRepeat]
  | n + 1 => by
      simp [v115WordRepeat, v115WordRepeat_length w n,
        Nat.succ_mul]

/--
Repeating a nonempty word n times gives a word of length at least n.
This avoids any arithmetic dependence on the actual positive word length.
-/
theorem v115WordRepeat_count_le_length
    (w : Word α)
    (hw : w ≠ [])
    (n : Nat) :
    n ≤ (v115WordRepeat w n).length := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hwlen : 0 < w.length :=
        List.length_pos_of_ne_nil hw
      simp only [v115WordRepeat, List.length_append]
      have hrec :
          n ≤ (v115WordRepeat w n).length :=
        ih
      omega

@[simp] theorem v115FixedHom_wordRepeat
    (H : FixedFiniteMonoidHom α M)
    (w : Word α) :
    ∀ n : Nat,
      H.h (v115WordRepeat w n) = (H.h w) ^ n
  | 0 => by
      simpa [v115WordRepeat] using H.map_nil
  | n + 1 => by
      rw [v115WordRepeat, H.map_append,
        v115FixedHom_wordRepeat H w n, pow_succ]

/-- Every positive power of an idempotent is itself. -/
theorem v115_idempotent_pow_succ
    {e : M}
    (hidem : e * e = e) :
    ∀ n : Nat, e ^ (n + 1) = e
  | 0 => by simp
  | n + 1 => by
      calc
        e ^ ((n + 1) + 1)
            = e ^ (n + 1) * e := by
                rw [pow_succ]
        _ = e * e := by
              rw [v115_idempotent_pow_succ hidem n]
        _ = e := hidem

/--
Reverse implication of v115 Proposition 3.5.

If equality under h_{k,l} on nonempty words implies equality under H, then
the positive image of H is locally trivial.
-/
theorem v115_positiveImageLocallyTrivial_of_fixedWindow_refinement
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat)
    (hrefines :
      V115NonemptyKernelRefines
        (fixedWindowMonoidHom (α := α) k l)
        H) :
    V115PositiveImageLocallyTrivial H := by
  intro e t he ht hidem
  rcases he with ⟨r, hrne, hre⟩
  rcases ht with ⟨z, hzne, hzt⟩
  let j : Nat := k + l + 1
  let R : Word α := v115WordRepeat r j
  have hj_le_R :
      j ≤ R.length := by
    dsimp [R]
    exact v115WordRepeat_count_le_length r hrne j
  have hkR : k ≤ R.length := by
    have hkj : k ≤ j := by
      dsimp [j]
      omega
    exact le_trans hkj hj_le_R
  have hlR : l ≤ R.length := by
    have hlj : l ≤ j := by
      dsimp [j]
      omega
    exact le_trans hlj hj_le_R
  let p : Word α := R.take k
  let a : Word α := R.drop k
  let b : Word α := R.take (R.length - l)
  let q : Word α := R.drop (R.length - l)
  have hp : p.length = k := by
    dsimp [p]
    simp [hkR]
  have hq : q.length = l := by
    dsimp [q]
    simp only [List.length_drop]
    omega
  have hleft : p ++ a = R := by
    dsimp [p, a]
    exact List.take_append_drop k R
  have hright : b ++ q = R := by
    dsimp [b, q]
    exact List.take_append_drop (R.length - l) R
  let xw : Word α := R ++ r ++ R
  let yw : Word α := R ++ z ++ R
  have hxne : xw ≠ [] := by
    dsimp [xw]
    simp [hrne]
  have hyne : yw ≠ [] := by
    dsimp [yw]
    simp [hzne]
  have hsame :
      SameFixedWindowSummary k l xw yw := by
    by_cases hsum : k + l = 0
    · have hk0 : k = 0 := by omega
      have hl0 : l = 0 := by omega
      simpa only [hk0, hl0] using
        (zero_words_sameFixedWindowSummary
          (List.length_pos_of_ne_nil hxne)
          (List.length_pos_of_ne_nil hyne))
    · have hpos : 0 < k + l :=
        Nat.pos_of_ne_zero hsum
      have hbase :=
        boundary_words_sameFixedWindowSummary
          (α := α)
          hpos p q
          (a ++ r ++ b)
          (a ++ z ++ b)
          hp hq
      have hxdecomp :
          xw = p ++ (a ++ r ++ b) ++ q := by
        dsimp [xw]
        calc
          R ++ r ++ R
              = (p ++ a) ++ r ++ (b ++ q) := by
                  rw [hleft, hright]
          _ = p ++ (a ++ r ++ b) ++ q := by
                simp [List.append_assoc]
      have hydecomp :
          yw = p ++ (a ++ z ++ b) ++ q := by
        dsimp [yw]
        calc
          R ++ z ++ R
              = (p ++ a) ++ z ++ (b ++ q) := by
                  rw [hleft, hright]
          _ = p ++ (a ++ z ++ b) ++ q := by
                simp [List.append_assoc]
      rw [hxdecomp, hydecomp]
      exact hbase
  have hwindow :
      (fixedWindowMonoidHom (α := α) k l).h xw =
        (fixedWindowMonoidHom (α := α) k l).h yw :=
    fixedWindowMonoidHom_respects
      (α := α) k l xw yw hsame
  have hHxy : H.h xw = H.h yw :=
    hrefines xw yw hxne hyne hwindow
  have hR : H.h R = e := by
    dsimp [R, j]
    rw [v115FixedHom_wordRepeat, hre]
    exact v115_idempotent_pow_succ hidem (k + l)
  have hxmap : H.h xw = e := by
    dsimp [xw]
    rw [H.map_append (R ++ r) R,
      H.map_append R r, hR, hre, hidem, hidem]
  have hymap : H.h yw = e * t * e := by
    dsimp [yw]
    rw [H.map_append (R ++ z) R,
      H.map_append R z, hR, hzt]
  calc
    e * t * e = H.h yw := hymap.symm
    _ = H.h xw := hHxy.symm
    _ = e := hxmap

/--
Every concrete fixed-window typing has locally trivial positive image.
This is the reverse-direction theorem specialized to the identity refinement.
-/
theorem v115_fixedWindow_positiveImageLocallyTrivial
    [Fintype α]
    (k l : Nat) :
    V115PositiveImageLocallyTrivial
      (fixedWindowMonoidHom (α := α) k l) := by
  apply
    v115_positiveImageLocallyTrivial_of_fixedWindow_refinement
      (fixedWindowMonoidHom (α := α) k l)
      k l
  intro x y _hx _hy hxy
  exact hxy

end V115LocallyTrivialWindows

end TCS1
end LeanCfgProject
