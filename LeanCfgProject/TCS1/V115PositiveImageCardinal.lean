import LeanCfgProject.TCS1.V115FinitePositivePowers

/-!
# TCS #1 v115: the |h(Sigma+)| prefix pigeonhole theorem

Pin XI.4.17 implies that the image of every positive word of length
n = |S| (S = h(Sigma+)) is idempotent in a finite locally-trivial
semigroup.  Here is a direct constructive finite proof of the bound.

Every nonempty prefix has a value in S.  Distinct prefixes of a word
with non-idempotent values have distinct h-values: otherwise their
intervening nonempty factor right-stabilizes the earlier prefix,
contradicting the stationary-idempotent theorem.

The |S| positive prefixes cannot all be non-idempotent because S also
contains a positive idempotent (obtained via the finite-power theorem).
Thus some prefix is idempotent.  The two-sided idempotent-ideal lemma
then makes the entire word idempotent.

This discharges the exact finite-semigroup premise isolated in the
v115 forward fixed-window reduction, with no extra postulates or placeholder proofs.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V115PositiveImageCardinal
variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- The cardinality of the positive image of H, as in v115 Proposition 3.5. -/
noncomputable def v115PositiveImageCard
    (H : FixedFiniteMonoidHom α M) : Nat := by
  classical
  exact Fintype.card {m : M // V115InPositiveImage H m}

/-- A nonempty alphabet guarantees a nonempty positive image. -/
theorem v115_positiveImageCard_pos
    [Nonempty α]
    (H : FixedFiniteMonoidHom α M) :
    0 < v115PositiveImageCard H := by
  classical
  let a : α := Classical.choice (inferInstance : Nonempty α)
  haveI : Nonempty {m : M // V115InPositiveImage H m} :=
    ⟨⟨H.h [a], ⟨[a], by simp, rfl⟩⟩⟩
  unfold v115PositiveImageCard
  exact Fintype.card_pos

/--
A collision between two distinct positive prefixes makes the
earlier one idempotent, by right-stationarity.
-/
theorem v115_colliding_prefix_idempotent
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (w : Word α)
    {i j : Nat}
    (hi : 0 < i)
    (hij : i < j)
    (hjw : j ≤ w.length)
    (heq : H.h (w.take i) = H.h (w.take j)) :
    H.h (w.take i) * H.h (w.take i) = H.h (w.take i) := by
  let p : Word α := w.take i
  let z : Word α := (w.take j).drop i
  have hpne : p ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    dsimp [p] at hlen
    simp only [List.length_take, List.length_nil] at hlen
    omega
  have hzlen : z.length = j - i := by
    dsimp [z]
    simp only [List.length_drop, List.length_take]
    rw [Nat.min_eq_left hjw]
  have hzne : z ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_nil] at hlen
    omega
  have htake : (w.take j).take i = p := by
    dsimp [p]
    simp only [List.take_take]
    rw [Nat.min_eq_left (Nat.le_of_lt hij)]
  have hsplit : w.take j = p ++ z := by
    calc
      w.take j =
          (w.take j).take i ++ (w.take j).drop i :=
        (List.take_append_drop i (w.take j)).symm
      _ = p ++ z := by rw [htake]
  have hpfix : H.h p * H.h z = H.h p := by
    calc
      H.h p * H.h z = H.h (p ++ z) :=
        (H.map_append p z).symm
      _ = H.h (w.take j) := by rw [hsplit]
      _ = H.h p := heq.symm
  exact
    v115_positiveImage_stationary_idempotent
      H hlocal ⟨p, hpne, rfl⟩ ⟨z, hzne, rfl⟩ hpfix

/--
Some nonempty prefix of a word of length |S| has idempotent image,
where S is the positive image of H.
-/
theorem v115_exists_idempotent_prefix_at_card
    [Nonempty α]
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (w : Word α)
    (hw : w.length = v115PositiveImageCard H) :
    ∃ i : Nat,
      0 < i ∧ i ≤ w.length ∧
      H.h (w.take i) * H.h (w.take i) = H.h (w.take i) := by
  classical
  let S : Type v := {m : M // V115InPositiveImage H m}
  let n := Fintype.card S
  have hw' : w.length = n := by
    simpa only [n, S, v115PositiveImageCard] using hw
  let a : α := Classical.choice (inferInstance : Nonempty α)
  have hletter : V115InPositiveImage H (H.h [a]) :=
    ⟨[a], by simp, rfl⟩
  obtain ⟨k, hk, hidem⟩ :=
    v115_exists_positive_idempotent_power (H.h [a])
  let e : S :=
    ⟨(H.h [a]) ^ k,
      v115_positiveImage_pow H hletter k hk⟩
  have he : e.val * e.val = e.val := hidem
  have hn : 0 < n := by
    haveI : Nonempty S := ⟨e⟩
    exact Fintype.card_pos
  have hprefix_nonempty (i : Fin n) :
      w.take (i.val + 1) ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_take, List.length_nil] at hlen
    have hle : i.val + 1 ≤ w.length := by omega
    omega
  let pref : Fin n → S := fun i =>
    ⟨H.h (w.take (i.val + 1)),
      ⟨w.take (i.val + 1), hprefix_nonempty i, rfl⟩⟩
  suffices hex :
      ∃ i : Fin n,
        (pref i).val * (pref i).val = (pref i).val by
    obtain ⟨i, hi⟩ := hex
    refine ⟨i.val + 1, by omega, by omega, ?_⟩
    exact hi
  by_contra hno
  have hnon (i : Fin n) :
      (pref i).val * (pref i).val ≠ (pref i).val := by
    intro hi
    exact hno ⟨i, hi⟩
  let T : Type v := {s : S // s.val * s.val ≠ s.val}
  let f : Fin n → T := fun i => ⟨pref i, hnon i⟩
  have hcard_lt : Fintype.card T < n := by
    have hp : ¬ (e.val * e.val ≠ e.val) := by
      intro hne
      exact hne he
    have hc :=
      Fintype.card_subtype_lt
        (p := fun s : S => s.val * s.val ≠ s.val)
        (x := e) hp
    simpa only [T, n] using hc
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hval : (pref i).val = (pref j).val :=
      congrArg (fun x : T => x.val.val) hij
    have hijne : i.val ≠ j.val := by
      intro heq
      apply hne
      exact Fin.ext heq
    rcases lt_or_gt_of_ne hijne with hlt | hgt
    · apply hnon i
      exact
        v115_colliding_prefix_idempotent
          H hlocal w
          (Nat.succ_pos _)
          (by omega)
          (by omega)
          hval
    · apply hnon j
      exact
        v115_colliding_prefix_idempotent
          H hlocal w
          (Nat.succ_pos _)
          (by omega)
          (by omega)
          hval.symm
  have hle : n ≤ Fintype.card T := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective f hinj
  omega

/--
Pin XI.4.17: every product of |S| positive-image elements is
idempotent, stated as a nonempty word of length |S|.
-/
theorem v115_locallyTrivial_length_card_idempotent
    [Nonempty α]
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    (w : Word α)
    (hw : w.length = v115PositiveImageCard H) :
    H.h w * H.h w = H.h w := by
  obtain ⟨i, hi, hiw, hidem⟩ :=
    v115_exists_idempotent_prefix_at_card H hlocal w hw
  have hprefix : w.take i ≠ [] := by
    intro hnil
    have hlen := congrArg List.length hnil
    simp only [List.length_take, List.length_nil] at hlen
    omega
  have hwhole :=
    v115_idempotent_factor_implies_word_idempotent
      H hlocal [] (w.take i) (w.drop i) hprefix hidem
  simpa only [List.nil_append, List.take_append_drop] using hwhole

/--
The missing forward implication in Proposition 3.5, with exactly
n = |h(Sigma+)| and no idempotence hypothesis.
-/
theorem v115_positiveImageLocallyTrivial_window_refines
    [Fintype α] [Nonempty α]
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H) :
    V115NonemptyKernelRefines
      (fixedWindowMonoidHom
        (α := α)
        (v115PositiveImageCard H)
        (v115PositiveImageCard H))
      H := by
  have hn : 0 < v115PositiveImageCard H :=
    v115_positiveImageCard_pos H
  apply v115_windowRefinement_of_lengthIdempotence
    H (v115PositiveImageCard H) hn hlocal
  intro p hp
  exact v115_locallyTrivial_length_card_idempotent H hlocal p hp

end V115PositiveImageCardinal
end TCS1
end LeanCfgProject
