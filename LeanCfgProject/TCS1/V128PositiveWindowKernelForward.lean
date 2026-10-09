import LeanCfgProject.TCS1.V128PositiveWindowKernelConverse

/-!
# TCS #1 v128: locally trivial positive image gives an explicit fixed window

This module closes the previously open forward direction of
Proposition `prop:li-window`.

The proof stays at the positive-word level used by the manuscript.  We first
count the finite positive image `h(Σ⁺)`.  A word of length
`|h(Σ⁺)| + 1` has two equal nonempty prefix types.  The intervening positive
factor has an idempotent power in the ambient finite monoid, which gives a
factorization of the whole boundary word through a positive-image
idempotent.  The already formalized local sandwich law is then upgraded to
the two-idempotent law `e * s * f = e * f`, and insertion of an arbitrary
middle word disappears between the two boundary factorizations.

This gives the exact explicit `(n,n)` window from v128, where
`n = |h(Σ⁺)| + 1`, without redoing the converse proved in CI #921/#922.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section PositiveWindowForward

variable {α : Type u} {M : Type v}
variable [Fintype α] [Monoid M] [Fintype M]

/-- The positive image of a fixed typing, represented as a finite subtype. -/
def PositiveImageElement
    (H : FixedFiniteMonoidHom α M) :=
  {m : M // ∃ w : Word α, w ≠ [] ∧ H.h w = m}

instance positiveImageElementFinite
    (H : FixedFiniteMonoidHom α M) :
    Finite (PositiveImageElement H) :=
  Finite.of_injective Subtype.val Subtype.coe_injective

noncomputable instance positiveImageElementFintype
    (H : FixedFiniteMonoidHom α M) :
    Fintype (PositiveImageElement H) := by
  classical
  exact Fintype.ofFinite _

/-- The manuscript quantity `|h(Σ⁺)|`. -/
noncomputable def positiveImageCard
    (H : FixedFiniteMonoidHom α M) : Nat :=
  Fintype.card (PositiveImageElement H)

/-- The explicit window size used in Proposition `prop:li-window`. -/
noncomputable def positiveWindowBound
    (H : FixedFiniteMonoidHom α M) : Nat :=
  positiveImageCard H + 1

/-- Repetition maps to the corresponding monoid power. -/
theorem v128RepeatWord_type_pow
    (H : FixedFiniteMonoidHom α M)
    (r : Word α) :
    ∀ n : Nat,
      H.h (v128RepeatWord r n) = (H.h r) ^ n := by
  intro n
  induction n with
  | zero =>
      simp [v128RepeatWord, H.map_nil]
  | succ n ih =>
      rw [v128RepeatWord, H.map_append, ih, pow_succ']

/-- A positive repetition of a nonempty word is nonempty. -/
theorem v128RepeatWord_ne_nil
    (r : Word α) (hr : r ≠ [])
    {n : Nat} (hn : 0 < n) :
    v128RepeatWord r n ≠ [] := by
  intro hnil
  have hlen :=
    v128RepeatWord_length_lower r hr n
  have hzero :
      (v128RepeatWord r n).length = 0 := by
    simpa [hnil]
  omega

/-- If right multiplication by x already fixes a, then every power of x
    fixes a as well. -/
theorem v128_mul_pow_eq_self
    (a x : M)
    (hax : a * x = a) :
    ∀ n : Nat, a * x ^ n = a := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, ← mul_assoc, ih, hax]

/-- Every element of a finite monoid has a positive idempotent power.

This is the small finite-semigroup ingredient needed below.  We prove it
internally from repetition of powers in a finite carrier, rather than adding
an external axiom for the Pin finite-semigroup fact. -/
theorem v128_exists_idempotent_power
    (x : M) :
    ∃ t : Nat, 0 < t ∧ x ^ t * x ^ t = x ^ t := by
  let f : Nat → M := fun n => x ^ (n + 1)
  obtain ⟨i, j, hij, hEq⟩ :=
    Finite.exists_ne_map_eq_of_infinite f
  have aux :
      ∀ {i j : Nat}, i < j →
        x ^ (i + 1) = x ^ (j + 1) →
        ∃ t : Nat, 0 < t ∧ x ^ t * x ^ t = x ^ t := by
    intro i j hij hEq
    let a : Nat := i + 1
    let d : Nat := j - i
    have ha : 0 < a := by
      dsimp [a]
      omega
    have hd : 0 < d := by
      dsimp [d]
      omega
    have had : a + d = j + 1 := by
      dsimp [a, d]
      omega
    have hbase : x ^ a = x ^ (a + d) := by
      simpa [a, had] using hEq
    have hperiodOne (n : Nat) (han : a ≤ n) :
        x ^ (n + d) = x ^ n := by
      calc
        x ^ (n + d) =
            x ^ ((a + d) + (n - a)) := by
              congr 1
              omega
        _ = x ^ (a + d) * x ^ (n - a) := by
              rw [pow_add]
        _ = x ^ a * x ^ (n - a) := by
              rw [← hbase]
        _ = x ^ (a + (n - a)) :=
              (pow_add x a (n - a)).symm
        _ = x ^ n := by
              congr 1
              omega
    have hperiodIter (n q : Nat) (han : a ≤ n) :
        x ^ (n + q * d) = x ^ n := by
      induction q with
      | zero =>
          simp
      | succ q ih =>
          calc
            x ^ (n + (q + 1) * d) =
                x ^ ((n + q * d) + d) := by
                  simp [Nat.add_mul, Nat.add_assoc]
            _ = x ^ (n + q * d) :=
                  hperiodOne (n + q * d) (by omega)
            _ = x ^ n := ih
    let t : Nat := a * d
    have hat : a ≤ t := by
      have hd1 : 1 ≤ d := Nat.succ_le_iff.mpr hd
      calc
        a = a * 1 := by simp
        _ ≤ a * d := Nat.mul_le_mul_left a hd1
    refine ⟨t, Nat.mul_pos ha hd, ?_⟩
    rw [← pow_add]
    have hper := hperiodIter t a hat
    simpa [t] using hper
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact aux hijlt (by simpa [f] using hEq)
  · exact aux hjilt (by simpa [f] using hEq.symm)

/-- A positive word factors, at the level of h-types, through a positive
idempotent once two distinct positive prefixes have the same h-type. -/
theorem v128_factorization_of_prefix_collision
    (H : FixedFiniteMonoidHom α M)
    (p : Word α)
    {n i j : Nat}
    (hp : p.length = n)
    (hi : i < n)
    (hj : j < n)
    (hij : i < j)
    (hEq :
      H.h (p.take (i + 1)) =
        H.h (p.take (j + 1))) :
    ∃ a e b : Word α,
      a ≠ [] ∧
      e ≠ [] ∧
      H.h e * H.h e = H.h e ∧
      H.h p = H.h a * H.h e * H.h b := by
  let a : Word α := p.take (i + 1)
  let pj : Word α := p.take (j + 1)
  let v : Word α := pj.drop (i + 1)
  let b : Word α := p.drop (j + 1)
  have hiLen : i + 1 ≤ p.length := by
    rw [hp]
    omega
  have hjLen : j + 1 ≤ p.length := by
    rw [hp]
    omega
  have hNested :
      pj.take (i + 1) = a := by
    dsimp [pj, a]
    rw [List.take_take]
    congr 1
    omega
  have hPrefixJ :
      a ++ v = pj := by
    calc
      a ++ v =
          pj.take (i + 1) ++ pj.drop (i + 1) := by
            rw [hNested]
      _ = pj := List.take_append_drop (i + 1) pj
  have hpjLen :
      pj.length = j + 1 := by
    dsimp [pj]
    simp [List.length_take, hjLen]
  have hvLen :
      v.length = j - i := by
    dsimp [v]
    rw [List.length_drop, hpjLen]
    omega
  have haNonempty : a ≠ [] := by
    intro hnil
    have hz := congrArg List.length hnil
    have haLen : a.length = i + 1 := by
      dsimp [a]
      simp [List.length_take, hiLen]
    rw [haLen] at hz
    simp at hz
  have hvNonempty : v ≠ [] := by
    intro hnil
    have hz := congrArg List.length hnil
    rw [hvLen] at hz
    simp at hz
    omega
  have hStab :
      H.h a * H.h v = H.h a := by
    calc
      H.h a * H.h v = H.h (a ++ v) :=
        (H.map_append a v).symm
      _ = H.h pj := by rw [hPrefixJ]
      _ = H.h a := by
        simpa [a, pj] using hEq.symm
  obtain ⟨t, htPos, htIdem⟩ :=
    v128_exists_idempotent_power (M := M) (H.h v)
  let e : Word α := v128RepeatWord v t
  have heType :
      H.h e = (H.h v) ^ t := by
    dsimp [e]
    exact v128RepeatWord_type_pow H v t
  have heNonempty : e ≠ [] := by
    dsimp [e]
    exact v128RepeatWord_ne_nil v hvNonempty htPos
  have heIdem :
      H.h e * H.h e = H.h e := by
    rw [heType]
    exact htIdem
  have hae :
      H.h a * H.h e = H.h a := by
    rw [heType]
    exact v128_mul_pow_eq_self (H.h a) (H.h v) hStab t
  have hFull :
      (a ++ v) ++ b = p := by
    calc
      (a ++ v) ++ b = pj ++ b := by rw [hPrefixJ]
      _ = p := by
        simpa [pj, b] using List.take_append_drop (j + 1) p
  refine ⟨a, e, b, haNonempty, heNonempty, heIdem, ?_⟩
  calc
    H.h p =
        (H.h a * H.h v) * H.h b := by
          rw [← hFull]
          simp only [H.map_append]
    _ = H.h a * H.h b := by
          rw [hStab]
    _ = (H.h a * H.h e) * H.h b := by
          rw [hae]
    _ = H.h a * H.h e * H.h b := rfl

/-- Every word of the manuscript boundary length
`|h(Σ⁺)| + 1` admits the idempotent factorization above. -/
theorem v128_positiveBoundary_factorization
    (H : FixedFiniteMonoidHom α M)
    (p : Word α)
    (hp : p.length = positiveWindowBound H) :
    ∃ a e b : Word α,
      a ≠ [] ∧
      e ≠ [] ∧
      H.h e * H.h e = H.h e ∧
      H.h p = H.h a * H.h e * H.h b := by
  classical
  let n : Nat := positiveWindowBound H
  have hp' : p.length = n := by
    simpa [n] using hp
  let f : Fin n → PositiveImageElement H := fun i =>
    ⟨H.h (p.take (i.val + 1)), by
      refine ⟨p.take (i.val + 1), ?_, rfl⟩
      have htake :
          (p.take (i.val + 1)).length = i.val + 1 := by
        rw [List.length_take]
        apply min_eq_left
        rw [hp']
        exact Nat.succ_le_of_lt i.isLt
      intro hnil
      have hz := congrArg List.length hnil
      rw [htake] at hz
      simp at hz⟩
  have hnotinj : ¬ Function.Injective f := by
    intro hinj
    have hle :
        n ≤ positiveImageCard H := by
      simpa [positiveImageCard] using
        (Fintype.card_le_of_injective f hinj)
    dsimp [n, positiveWindowBound] at hle
    omega
  obtain ⟨i, j, hfij, hij⟩ :=
    Function.not_injective_iff.mp hnotinj
  have hval :
      H.h (p.take (i.val + 1)) =
        H.h (p.take (j.val + 1)) := by
    exact congrArg Subtype.val hfij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact
      v128_factorization_of_prefix_collision
        H p hp' i.isLt j.isLt hijlt hval
  · exact
      v128_factorization_of_prefix_collision
        H p hp' j.isLt i.isLt hjilt hval.symm

/-- The local sandwich law `e s e = e` on positive representatives implies
the two-idempotent law `e s f = e f` needed by the window proof. -/
theorem positiveImageSandwichTrivial_esf
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H)
    (eWord fWord sWord : Word α)
    (hePos : eWord ≠ [])
    (hfPos : fWord ≠ [])
    (hsPos : sWord ≠ [])
    (heIdem :
      H.h eWord * H.h eWord = H.h eWord)
    (hfIdem :
      H.h fWord * H.h fWord = H.h fWord) :
    H.h eWord * H.h sWord * H.h fWord =
      H.h eWord * H.h fWord := by
  have hefeRaw :=
    hlocal eWord fWord hePos hfPos heIdem
  have hefe :
      H.h eWord * H.h fWord * H.h eWord =
        H.h eWord := by
    simpa only [H.map_append] using hefeRaw
  have hfefRaw :=
    hlocal fWord eWord hfPos hePos hfIdem
  have hfef :
      H.h fWord * H.h eWord * H.h fWord =
        H.h fWord := by
    simpa only [H.map_append] using hfefRaw
  let gWord : Word α := eWord ++ fWord
  let tWord : Word α := eWord ++ sWord ++ fWord
  have hgPos : gWord ≠ [] := by
    intro hnil
    have hz := congrArg List.length hnil
    simp only [gWord, List.length_append, List.length_nil] at hz
    have heLen := List.length_pos_of_ne_nil hePos
    omega
  have htPos : tWord ≠ [] := by
    intro hnil
    have hz := congrArg List.length hnil
    simp only [tWord, List.length_append, List.length_nil] at hz
    have heLen := List.length_pos_of_ne_nil hePos
    omega
  have hgIdem :
      H.h gWord * H.h gWord = H.h gWord := by
    dsimp [gWord]
    simp only [H.map_append]
    calc
      (H.h eWord * H.h fWord) *
          (H.h eWord * H.h fWord) =
        (H.h eWord * H.h fWord * H.h eWord) *
          H.h fWord := by
            simp [mul_assoc]
      _ = H.h eWord * H.h fWord := by
            rw [hefe]
  have hgtgRaw :=
    hlocal gWord tWord hgPos htPos hgIdem
  have hgtg :
      (H.h eWord * H.h fWord) *
          (H.h eWord * H.h sWord * H.h fWord) *
          (H.h eWord * H.h fWord) =
        H.h eWord * H.h fWord := by
    simpa only [gWord, tWord, H.map_append] using hgtgRaw
  have hcollapse :
      (H.h eWord * H.h fWord) *
          (H.h eWord * H.h sWord * H.h fWord) *
          (H.h eWord * H.h fWord) =
        H.h eWord * H.h sWord * H.h fWord := by
    calc
      (H.h eWord * H.h fWord) *
          (H.h eWord * H.h sWord * H.h fWord) *
          (H.h eWord * H.h fWord) =
        (H.h eWord * H.h fWord * H.h eWord) *
          H.h sWord *
          (H.h fWord * H.h eWord * H.h fWord) := by
            simp [mul_assoc]
      _ = H.h eWord * H.h sWord * H.h fWord := by
            rw [hefe, hfef]
  exact hcollapse.symm.trans hgtg

/-- Local triviality of the positive image makes an arbitrary middle word
invisible between two boundaries of length `|h(Σ⁺)|+1`. -/
theorem positiveImageTrivial_implies_boundary_at_explicit_window
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H) :
    PositiveWindowBoundaryInvariant
      H (positiveWindowBound H) (positiveWindowBound H) := by
  intro p q m₁ m₂ hp hq _hx _hy
  obtain ⟨a, e, b, haPos, hePos, heIdem, hpFact⟩ :=
    v128_positiveBoundary_factorization H p hp
  obtain ⟨c, f, d, hcPos, hfPos, hfIdem, hqFact⟩ :=
    v128_positiveBoundary_factorization H q hq
  have collapse (m : Word α) :
      H.h (p ++ m ++ q) =
        H.h a * (H.h e * H.h f) * H.h d := by
    let sWord : Word α := b ++ m ++ c
    have hsPos : sWord ≠ [] := by
      intro hnil
      have hz := congrArg List.length hnil
      simp only [sWord, List.length_append, List.length_nil] at hz
      have hcLen := List.length_pos_of_ne_nil hcPos
      omega
    have hesf :=
      positiveImageSandwichTrivial_esf
        H hlocal e f sWord
        hePos hfPos hsPos heIdem hfIdem
    calc
      H.h (p ++ m ++ q) =
          H.h p * H.h m * H.h q := by
            simp only [H.map_append]
      _ =
          (H.h a * H.h e * H.h b) *
            H.h m *
            (H.h c * H.h f * H.h d) := by
              rw [hpFact, hqFact]
      _ =
          H.h a *
            (H.h e * H.h sWord * H.h f) *
            H.h d := by
              simp only [sWord, H.map_append]
              simp [mul_assoc]
      _ =
          H.h a * (H.h e * H.h f) * H.h d := by
            rw [hesf]
  exact (collapse m₁).trans (collapse m₂).symm

/-- The missing forward implication of Proposition `prop:li-window`:
if the positive image is locally trivial, the explicit
`(n,n)` fixed window with `n=|h(Σ⁺)|+1` refines h on positive words. -/
theorem positiveImageTrivial_implies_positiveWindowKernelRefines
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H) :
    PositiveWindowKernelRefines
      H (positiveWindowBound H) (positiveWindowBound H) := by
  exact
    positiveWindowBoundary_implies_kernel_refines
      H (positiveWindowBound H) (positiveWindowBound H)
      (positiveImageTrivial_implies_boundary_at_explicit_window
        H hlocal)

/-- Positive-word kernel refinement is enough to recover the full
`RespectsFixedWindowSummary` contract.  Short summaries are literal word
equality, while long summaries are necessarily positive and may therefore use
the positive-word refinement hypothesis. -/
theorem respectsFixedWindowSummary_of_positiveWindowKernelRefines
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat)
    (href : PositiveWindowKernelRefines H k l) :
    RespectsFixedWindowSummary H k l := by
  intro x y hsummary
  rcases hsummary with hshort | hlong
  · simpa [hshort.2]
  · have hthresholdPos : 0 < fixedWindowThreshold k l := by
      simp [fixedWindowThreshold]
    rcases hlong with
      ⟨hxLong, hyLong, p, q, m₁, m₂,
        hp, hq, hx, hy⟩
    have hxPos : x ≠ [] := by
      intro hxNil
      subst x
      simp [fixedWindowThreshold] at hxLong
      omega
    have hyPos : y ≠ [] := by
      intro hyNil
      subst y
      simp [fixedWindowThreshold] at hyLong
      omega
    apply href x y hxPos hyPos
    apply
      fixedWindowMonoidHom_respects
        (α := α) k l x y
    exact Or.inr
      ⟨hxLong, hyLong, p, q, m₁, m₂,
        hp, hq, hx, hy⟩

/-- A locally trivial positive image therefore satisfies the exact
fixed-window semantic contract at the explicit manuscript window
`n=|h(Σ⁺)|+1`. -/
theorem positiveImageTrivial_implies_respects_explicitWindow
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H) :
    RespectsFixedWindowSummary
      H (positiveWindowBound H) (positiveWindowBound H) := by
  exact
    respectsFixedWindowSummary_of_positiveWindowKernelRefines
      H (positiveWindowBound H) (positiveWindowBound H)
      (positiveImageTrivial_implies_positiveWindowKernelRefines
        H hlocal)

/-- Exact positive-image criterion, now in both directions, with the explicit
window on the forward side. -/
theorem positiveImageTrivial_iff_explicitWindowKernelRefines
    (H : FixedFiniteMonoidHom α M) :
    PositiveImageSandwichTrivial H ↔
      PositiveWindowKernelRefines
        H (positiveWindowBound H) (positiveWindowBound H) := by
  constructor
  · exact
      positiveImageTrivial_implies_positiveWindowKernelRefines H
  · exact
      positiveWindowKernel_refines_implies_positiveImageTrivial
        H (positiveWindowBound H) (positiveWindowBound H)

/-- Equivalent existential form of the positive-image/fixed-window criterion. -/
theorem positiveImageTrivial_iff_exists_positiveWindowKernelRefines
    (H : FixedFiniteMonoidHom α M) :
    PositiveImageSandwichTrivial H ↔
      ∃ k l : Nat, PositiveWindowKernelRefines H k l := by
  constructor
  · intro hlocal
    exact
      ⟨positiveWindowBound H, positiveWindowBound H,
        positiveImageTrivial_implies_positiveWindowKernelRefines
          H hlocal⟩
  · rintro ⟨k, l, href⟩
    exact
      positiveWindowKernel_refines_implies_positiveImageTrivial
        H k l href

/-- Every concrete fixed-window typing has a locally trivial positive image.
This reuses the already verified kernel=>local-trivial direction at the
identity refinement. -/
theorem fixedWindow_positiveImageTrivial
    (k l : Nat) :
    PositiveImageSandwichTrivial
      (fixedWindowMonoidHom (α := α) k l) := by
  apply
    positiveWindowKernel_refines_implies_positiveImageTrivial
      (fixedWindowMonoidHom (α := α) k l) k l
  intro x y _hx _hy hxy
  exact hxy

/-- Pointwise forward half of the manuscript class-union statement:
a language substitutable for a locally trivial fixed typing is substitutable
for the explicit fixed window. -/
theorem fixedWindowSubstitutable_of_positiveImageTrivial
    (H : FixedFiniteMonoidHom α M)
    (hlocal : PositiveImageSandwichTrivial H)
    (L : Set (Word α))
    (hsub : FixedHSubstitutable H L) :
    FixedWindowSubstitutable
      (positiveWindowBound H) (positiveWindowBound H) L := by
  exact
    fixedWindowSubstitutable_of_positiveWindowKernelRefines
      H (positiveWindowBound H) (positiveWindowBound H)
      (positiveImageTrivial_implies_positiveWindowKernelRefines
        H hlocal)
      L hsub

/-- Pointwise reverse half of the manuscript class-union statement:
a fixed-window-substitutable language is fixed-h substitutable for the
concrete window typing, whose positive image is locally trivial. -/
theorem fixedWindowSubstitutable_has_locallyTrivialTyping
    (k l : Nat)
    (L : Set (Word α))
    (hsub : FixedWindowSubstitutable k l L) :
    PositiveImageSandwichTrivial
        (fixedWindowMonoidHom (α := α) k l)
      ∧
    FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l) L := by
  constructor
  · exact fixedWindow_positiveImageTrivial (α := α) k l
  · exact
      (fixedWindowSubstitutable_iff_fixedHSubstitutable
        k l L).mp hsub

end PositiveWindowForward

end TCS1
end LeanCfgProject
