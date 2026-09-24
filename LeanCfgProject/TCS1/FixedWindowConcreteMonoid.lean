import LeanCfgProject.TCS1.FixedWindowConcreteSummary

/-!
# TCS #1 v68: concrete fixed-window monoid

This module completes the representation-level part of Proposition 3.2.
The carrier is exactly the image of the tagged fixed-window summary.  The
multiplication is the four-case multiplication from the manuscript, and the
summary map is proved to preserve concatenation.  Surjectivity then makes
associativity and the identity laws immediate from word concatenation.

The resulting `FixedFiniteMonoidHom` both respects and reflects
`SameFixedWindowSummary`.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section FixedWindowConcreteMonoid

variable {α : Type u}

/-- Taking n letters after truncating the right operand to n letters is harmless. -/
theorem take_append_take_right
    (x y : Word α) (n : Nat) :
    (x ++ y.take n).take n =
      (x ++ y).take n := by
  simp [List.take_append, List.take_take, Nat.sub_le]

/-- The last n letters of x++y only need the last n letters of x. -/
theorem rtake_append_rtake_left
    (x y : Word α) (n : Nat) :
    (x.rtake n ++ y).rtake n =
      (x ++ y).rtake n := by
  simp only [List.rtake_eq_reverse_take_reverse,
    List.reverse_append, List.reverse_reverse]
  congr 1
  exact
    take_append_take_right
      y.reverse x.reverse n

/-- If the right operand already has n letters, it supplies the whole suffix. -/
theorem rtake_append_of_le_right
    (x y : Word α) (n : Nat)
    (h : n ≤ y.length) :
    (x ++ y).rtake n = y.rtake n := by
  simp only [List.rtake_eq_reverse_take_reverse,
    List.reverse_append]
  congr 1
  exact
    List.take_append_of_le_length
      (by simpa using h)

/-- Prefix vector when only the direct length inequality is available. -/
def prefixVectorOfLe
    (w : Word α) (k : Nat)
    (hk : k ≤ w.length) :
    List.Vector α k :=
  ⟨w.take k, by
    simp [List.length_take, hk]⟩

/-- Suffix vector when only the direct length inequality is available. -/
def suffixVectorOfLe
    (w : Word α) (l : Nat)
    (hl : l ≤ w.length) :
    List.Vector α l :=
  ⟨w.rtake l, by
    simp [List.rtake, List.length_drop]
    omega⟩

/--
The four-case multiplication on tagged states from Proposition 3.2.
Only its restriction to the image is used for the monoid carrier.
-/
def fixedWindowRawMul
    (k l : Nat) :
    FixedWindowRawState α k l →
      FixedWindowRawState α k l →
      FixedWindowRawState α k l
  | Sum.inl sx, Sum.inl sy =>
      fixedWindowRawSummary k l
        (sx.2.toList ++ sy.2.toList)
  | Sum.inl sx, Sum.inr z =>
      Sum.inr
        (prefixVectorOfLe
          (sx.2.toList ++ z.1.toList) k
          (by
            have hp : z.1.toList.length = k :=
              z.1.2
            simp only [List.length_append]
            omega),
         z.2)
  | Sum.inr z, Sum.inl sy =>
      Sum.inr
        (z.1,
         suffixVectorOfLe
          (z.2.toList ++ sy.2.toList) l
          (by
            have hq : z.2.toList.length = l :=
              z.2.2
            simp only [List.length_append]
            omega))
  | Sum.inr z, Sum.inr z' =>
      Sum.inr (z.1, z'.2)

/-- Long words have enough letters for both window components. -/
theorem fixedWindow_sum_le_of_cut
    {k l : Nat} {w : Word α}
    (hcut :
      fixedWindowThreshold k l ≤ w.length) :
    k + l ≤ w.length := by
  have hsum :
      k + l ≤ fixedWindowThreshold k l := by
    unfold fixedWindowThreshold
    omega
  exact le_trans hsum hcut

/--
The concrete four-case multiplication computes the summary of concatenation.
This is the direct Lean counterpart of the four displayed equations in
Proposition 3.2.
-/
theorem fixedWindowRawSummary_append
    (k l : Nat)
    (x y : Word α) :
    fixedWindowRawSummary k l (x ++ y) =
      fixedWindowRawMul k l
        (fixedWindowRawSummary k l x)
        (fixedWindowRawSummary k l y) := by
  by_cases hx :
      x.length < fixedWindowThreshold k l
  · by_cases hy :
        y.length < fixedWindowThreshold k l
    · simp [fixedWindowRawMul,
        fixedWindowRawSummary, hx, hy]
    · have hycut :
          fixedWindowThreshold k l ≤ y.length :=
        Nat.le_of_not_gt hy
      have hxycut :
          fixedWindowThreshold k l ≤ (x ++ y).length := by
        simp only [List.length_append]
        omega
      have hxy :
          ¬ (x ++ y).length < fixedWindowThreshold k l :=
        not_lt_of_ge hxycut
      have hfity :=
        fixedWindow_sum_le_of_cut
          (α := α) hycut
      have hfitxy :=
        fixedWindow_sum_le_of_cut
          (α := α) hxycut
      unfold fixedWindowRawSummary
      rw [dif_neg hxy, dif_pos hx, dif_neg hy]
      simp only [fixedWindowRawMul]
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Subtype.ext
        dsimp [fixedWindowPrefixVector, prefixVectorOfLe]
        exact
          (take_append_take_right x y k).symm
      · apply Subtype.ext
        dsimp [fixedWindowSuffixVector]
        change (x ++ y).rtake l = y.rtake l
        exact
          rtake_append_of_le_right x y l
            (by omega)
  · have hxcut :
        fixedWindowThreshold k l ≤ x.length :=
      Nat.le_of_not_gt hx
    have hfitx :=
      fixedWindow_sum_le_of_cut
        (α := α) hxcut
    by_cases hy :
        y.length < fixedWindowThreshold k l
    · have hxycut :
          fixedWindowThreshold k l ≤ (x ++ y).length := by
        simp only [List.length_append]
        omega
      have hxy :
          ¬ (x ++ y).length < fixedWindowThreshold k l :=
        not_lt_of_ge hxycut
      have hfitxy :=
        fixedWindow_sum_le_of_cut
          (α := α) hxycut
      unfold fixedWindowRawSummary
      rw [dif_neg hxy, dif_neg hx, dif_pos hy]
      simp only [fixedWindowRawMul]
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Subtype.ext
        dsimp [fixedWindowPrefixVector]
        exact
          List.take_append_of_le_length
            (by omega)
      · apply Subtype.ext
        dsimp [fixedWindowSuffixVector, suffixVectorOfLe]
        change
          (x ++ y).rtake l =
            (x.rtake l ++ y).rtake l
        exact
          (rtake_append_rtake_left x y l).symm
    · have hycut :
          fixedWindowThreshold k l ≤ y.length :=
        Nat.le_of_not_gt hy
      have hxycut :
          fixedWindowThreshold k l ≤ (x ++ y).length := by
        simp only [List.length_append]
        omega
      have hxy :
          ¬ (x ++ y).length < fixedWindowThreshold k l :=
        not_lt_of_ge hxycut
      have hfity :=
        fixedWindow_sum_le_of_cut
          (α := α) hycut
      have hfitxy :=
        fixedWindow_sum_le_of_cut
          (α := α) hxycut
      unfold fixedWindowRawSummary
      rw [dif_neg hxy, dif_neg hx, dif_neg hy]
      simp only [fixedWindowRawMul]
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Subtype.ext
        dsimp [fixedWindowPrefixVector]
        exact
          List.take_append_of_le_length
            (by omega)
      · apply Subtype.ext
        dsimp [fixedWindowSuffixVector]
        change (x ++ y).rtake l = y.rtake l
        exact
          rtake_append_of_le_right x y l
            (by omega)

/-- The monoid carrier is exactly the image M_{k,l}=h_{k,l}(Sigma*). -/
abbrev FixedWindowMonoid
    (α : Type u) (k l : Nat) :=
  {s : FixedWindowRawState α k l //
    ∃ w : Word α,
      fixedWindowRawSummary k l w = s}

noncomputable instance fixedWindowMonoidFintype
    [Fintype α] (k l : Nat) :
    Fintype (FixedWindowMonoid α k l) := by
  classical
  exact Fintype.ofFinite _

/-- Multiplication on the image carrier. -/
def fixedWindowMul
    (k l : Nat)
    (a b : FixedWindowMonoid α k l) :
    FixedWindowMonoid α k l := by
  refine
    ⟨fixedWindowRawMul k l a.1 b.1, ?_⟩
  rcases a.2 with ⟨x, hx⟩
  rcases b.2 with ⟨y, hy⟩
  refine ⟨x ++ y, ?_⟩
  calc
    fixedWindowRawSummary k l (x ++ y)
        =
      fixedWindowRawMul k l
        (fixedWindowRawSummary k l x)
        (fixedWindowRawSummary k l y) :=
      fixedWindowRawSummary_append k l x y
    _ =
      fixedWindowRawMul k l a.1 b.1 := by
      rw [hx, hy]

/-- Identity state, namely the summary of lambda. -/
def fixedWindowOne
    (k l : Nat) :
    FixedWindowMonoid α k l :=
  ⟨fixedWindowRawSummary k l [],
    ⟨[], rfl⟩⟩

instance fixedWindowMonoidInst
    (k l : Nat) :
    Monoid (FixedWindowMonoid α k l) where
  one := fixedWindowOne k l
  mul := fixedWindowMul k l
  one_mul a := by
    apply Subtype.ext
    rcases a.2 with ⟨x, hx⟩
    change
      fixedWindowRawMul k l
          (fixedWindowRawSummary k l []) a.1 =
        a.1
    rw [← hx]
    rw [← fixedWindowRawSummary_append]
    rfl
  mul_one a := by
    apply Subtype.ext
    rcases a.2 with ⟨x, hx⟩
    change
      fixedWindowRawMul k l
          a.1 (fixedWindowRawSummary k l []) =
        a.1
    rw [← hx]
    rw [← fixedWindowRawSummary_append]
    simp
  mul_assoc a b c := by
    apply Subtype.ext
    rcases a.2 with ⟨x, hx⟩
    rcases b.2 with ⟨y, hy⟩
    rcases c.2 with ⟨z, hz⟩
    change
      fixedWindowRawMul k l
          (fixedWindowRawMul k l a.1 b.1) c.1 =
        fixedWindowRawMul k l
          a.1 (fixedWindowRawMul k l b.1 c.1)
    rw [← hx, ← hy, ← hz]
    rw [← fixedWindowRawSummary_append k l x y]
    rw [← fixedWindowRawSummary_append k l (x ++ y) z]
    rw [← fixedWindowRawSummary_append k l y z]
    rw [← fixedWindowRawSummary_append k l x (y ++ z)]
    simp [List.append_assoc]

/-- The concrete finite-monoid homomorphism h_{k,l}. -/
noncomputable def fixedWindowMonoidHom
    [Fintype α]
    (k l : Nat) :
    FixedFiniteMonoidHom α
      (FixedWindowMonoid α k l) := by
  classical
  refine
    { h := fun w =>
        ⟨fixedWindowRawSummary k l w,
          ⟨w, rfl⟩⟩
      map_nil := ?_
      map_append := ?_ }
  · rfl
  · intro x y
    apply Subtype.ext
    exact fixedWindowRawSummary_append k l x y

/-- The concrete summary map is onto its image carrier, as in the manuscript. -/
theorem fixedWindowMonoidHom_surjective
    [Fintype α]
    (k l : Nat) :
    Function.Surjective
      (fixedWindowMonoidHom
        (α := α) k l).h := by
  intro s
  rcases s.2 with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  exact hw

/-- h_{k,l} respects the semantic fixed-window summary. -/
theorem fixedWindowMonoidHom_respects
    [Fintype α]
    (k l : Nat) :
    RespectsFixedWindowSummary
      (fixedWindowMonoidHom
        (α := α) k l)
      k l := by
  intro x y hsame
  apply Subtype.ext
  exact
    fixedWindowRawSummary_eq_of_same
      (α := α) hsame

/-- h_{k,l} also reflects the semantic fixed-window summary. -/
theorem fixedWindowMonoidHom_reflects
    [Fintype α]
    (k l : Nat) :
    ReflectsFixedWindowSummary
      (fixedWindowMonoidHom
        (α := α) k l)
      k l := by
  intro x y hxy
  apply
    sameFixedWindowSummary_of_rawSummary_eq
      (α := α)
  exact congrArg Subtype.val hxy

end FixedWindowConcreteMonoid

end TCS1
end LeanCfgProject
