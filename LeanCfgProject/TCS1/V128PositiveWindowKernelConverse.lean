import LeanCfgProject.TCS1.V128PositiveWindowKernel

/-!
# TCS #1 v128: kernel-refinement entails positive-image local triviality

Proposition prop:li-window, converse direction: if some fixed-window
typing refines H on nonempty words, then every idempotent e in the positive
image satisfies e s e = e for each s in the positive image.

The algebraic identity is proved directly, without assuming Pin's separate
finite-semigroup forward-direction factorization. A repeated nonempty word
realizes an idempotent at an arbitrarily long left/right frame, and the
existing fixed-window summary multiplication erases the middle.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section PositiveWindowConverse

variable {α : Type u} {M : Type v}
variable [Fintype α] [Monoid M] [Fintype M]

/-- Repeat a word n times, with an explicit concatenation recursion. -/
def v128RepeatWord (r : Word α) : Nat → Word α
  | 0 => []
  | n + 1 => r ++ v128RepeatWord r n

/-- A nonempty word repeated n times has at least n symbols. -/
theorem v128RepeatWord_length_lower
    (r : Word α) (hr : r ≠ []) (n : Nat) :
    n ≤ (v128RepeatWord r n).length := by
  induction n with
  | zero =>
      simp [v128RepeatWord]
  | succ n ih =>
      have hpos : 0 < r.length := List.length_pos_of_ne_nil hr
      change n + 1 ≤ (r ++ v128RepeatWord r n).length
      simp only [List.length_append]
      omega

/-- Repeating a word of idempotent H-type retains exactly that type. -/
theorem v128RepeatWord_type_succ
    (H : FixedFiniteMonoidHom α M)
    (r : Word α) (n : Nat)
    (he : H.h r * H.h r = H.h r) :
    H.h (v128RepeatWord r (n + 1)) = H.h r := by
  induction n with
  | zero =>
      simp [v128RepeatWord, H.map_append, H.map_nil]
  | succ n ih =>
      change H.h (r ++ v128RepeatWord r (n + 1)) = H.h r
      rw [H.map_append, ih, he]

/-- Once both exterior words are long enough, the concrete fixed-window
    summary of p ++ middle ++ q is independent of middle. -/
theorem v128FixedWindow_long_frame_middle_independent
    (k l : Nat)
    (p q m₁ m₂ : Word α)
    (hp : fixedWindowThreshold k l ≤ p.length)
    (hq : fixedWindowThreshold k l ≤ q.length) :
    (fixedWindowMonoidHom (α := α) k l).h (p ++ m₁ ++ q) =
      (fixedWindowMonoidHom (α := α) k l).h (p ++ m₂ ++ q) := by
  apply Subtype.ext
  have hpfit : k + l ≤ p.length :=
    fixedWindow_sum_le_of_cut (α := α) hp
  have hqfit : k + l ≤ q.length :=
    fixedWindow_sum_le_of_cut (α := α) hq
  have hpraw :
      fixedWindowRawSummary k l p =
        Sum.inr
          (fixedWindowPrefixVector p k l hpfit,
           fixedWindowSuffixVector p k l hpfit) := by
    simp [fixedWindowRawSummary, not_lt_of_ge hp]
  have hqraw :
      fixedWindowRawSummary k l q =
        Sum.inr
          (fixedWindowPrefixVector q k l hqfit,
           fixedWindowSuffixVector q k l hqfit) := by
    simp [fixedWindowRawSummary, not_lt_of_ge hq]
  have hrewrite (m : Word α) :
      fixedWindowRawSummary k l (p ++ m ++ q) =
        fixedWindowRawMul k l
          (fixedWindowRawMul k l
            (fixedWindowRawSummary k l p)
            (fixedWindowRawSummary k l m))
          (fixedWindowRawSummary k l q) := by
    rw [fixedWindowRawSummary_append k l (p ++ m) q,
      fixedWindowRawSummary_append k l p m]
  change
    fixedWindowRawSummary k l (p ++ m₁ ++ q) =
      fixedWindowRawSummary k l (p ++ m₂ ++ q)
  rw [hrewrite m₁, hrewrite m₂]
  cases hm₁ : fixedWindowRawSummary k l m₁ <;>
    cases hm₂ : fixedWindowRawSummary k l m₂ <;>
      simp [hpraw, hqraw, hm₁, hm₂, fixedWindowRawMul]

/-- A fixed-window kernel inclusion forces the idempotent sandwich identity.
    The middle z may even be epsilon (then the identity is immediate). -/
theorem positiveWindowKernel_refines_implies_idempotent_sandwich
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat)
    (href : PositiveWindowKernelRefines H k l)
    (r z : Word α)
    (hr : r ≠ [])
    (he : H.h r * H.h r = H.h r) :
    H.h (r ++ z ++ r) = H.h r := by
  let t := fixedWindowThreshold k l
  let p : Word α := v128RepeatWord r (t + 1)
  have htpos : 0 < t := by
    dsimp [t, fixedWindowThreshold]
    omega
  have hlen : t + 1 ≤ p.length :=
    v128RepeatWord_length_lower r hr (t + 1)
  have hlong : fixedWindowThreshold k l ≤ p.length := by
    dsimp [t] at hlen
    omega
  have hpnonempty : p ≠ [] := by
    intro h
    have hzero : p.length = 0 := by simpa [h]
    omega
  have hx : p ++ z ++ p ≠ [] := by
    intro h
    have hzero := congrArg List.length h
    simp only [List.length_append, List.length_nil] at hzero
    have hp : 0 < p.length := List.length_pos_of_ne_nil hpnonempty
    omega
  have hy : p ++ p ≠ [] := by
    intro h
    have hzero := congrArg List.length h
    simp only [List.length_append, List.length_nil] at hzero
    have hp : 0 < p.length := List.length_pos_of_ne_nil hpnonempty
    omega
  have hw :
      (fixedWindowMonoidHom (α := α) k l).h (p ++ z ++ p) =
        (fixedWindowMonoidHom (α := α) k l).h (p ++ p) := by
    simpa only [List.append_nil] using
      v128FixedWindow_long_frame_middle_independent
        k l p p z [] hlong hlong
  have htyp := href (p ++ z ++ p) (p ++ p) hx hy hw
  have hcalc : H.h p * H.h z * H.h p = H.h p * H.h p := by
    simpa only [H.map_append] using htyp
  have htypep : H.h p = H.h r :=
    v128RepeatWord_type_succ H r t he
  rw [htypep] at hcalc
  calc
    H.h (r ++ z ++ r) = H.h r * H.h z * H.h r := by
      simp only [H.map_append]
    _ = H.h r * H.h r := hcalc
    _ = H.h r := he

/-- The positive image semigroup is locally trivial, expressed entirely
    by word-representatives of positive-image idempotents and elements. -/
def PositiveImageSandwichTrivial
    (H : FixedFiniteMonoidHom α M) : Prop :=
  ∀ r z : Word α,
    r ≠ [] → z ≠ [] →
    H.h r * H.h r = H.h r →
    H.h (r ++ z ++ r) = H.h r

/-- Converse of v128 prop:li-window, at its exact positive-image
    equational strength. No external finite semigroup theorem is needed. -/
theorem positiveWindowKernel_refines_implies_positiveImageTrivial
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat)
    (href : PositiveWindowKernelRefines H k l) :
    PositiveImageSandwichTrivial H := by
  intro r z hr _hz he
  exact positiveWindowKernel_refines_implies_idempotent_sandwich
    H k l href r z hr he

end PositiveWindowConverse

end TCS1
end LeanCfgProject
