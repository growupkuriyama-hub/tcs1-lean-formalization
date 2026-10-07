import LeanCfgProject.TCS1.V115PositiveIdempotentIdeal
import Mathlib.Topology.Algebra.Semigroup

/-!
# TCS #1 v115: finite positive powers and stationary prefixes

A finite semigroup has a positive idempotent power of every element.
We invoke the mathlib compact-semigroup idempotent theorem on the finite
discrete set of *strictly positive powers*, ensuring that the resulting
power is positive (so it belongs to h(Sigma+) even when 1 is outside it).

Under local triviality, an element p in the positive image that is
stabilized on the right by a positive element t must be idempotent.
This is the nontrivial collision step for the bounded-prefix/pigeonhole
proof of Pin XI.4.17.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V115FinitePositivePowers

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Each element of a finite monoid has an idempotent *positive* power. -/
theorem v115_exists_positive_idempotent_power (t : M) :
    ∃ k : Nat, 0 < k ∧ (t ^ k) * (t ^ k) = t ^ k := by
  classical
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  let S : Set M := { x | ∃ k : Nat, 0 < k ∧ t ^ k = x }
  have hS : S.Nonempty := by
    refine ⟨t, 1, by omega, ?_⟩
    simp
  have hcompact : IsCompact S := (Set.toFinite S).isCompact
  have hmul : ∀ᵉ (x ∈ S) (y ∈ S), x * y ∈ S := by
    intro x hx y hy
    obtain ⟨k, hk, hx⟩ := hx
    obtain ⟨l, hl, hy⟩ := hy
    refine ⟨k + l, by omega, ?_⟩
    calc
      t ^ (k + l) = t ^ k * t ^ l := pow_add t k l
      _ = x * y := by rw [hx, hy]
  obtain ⟨e, ⟨k, hk, hpow⟩, he⟩ :=
    exists_idempotent_in_compact_subsemigroup
      (fun _ : M => continuous_of_discreteTopology)
      S hS hcompact hmul
  exact ⟨k, hk, by simpa only [hpow] using he⟩

/-- Positive image is also closed under strictly positive powers. -/
theorem v115_positiveImage_pow
    (H : FixedFiniteMonoidHom α M)
    {t : M}
    (ht : V115InPositiveImage H t)
    (k : Nat)
    (hk : 0 < k) :
    V115InPositiveImage H (t ^ k) := by
  obtain ⟨r, hr, hrt⟩ := ht
  refine ⟨v115WordRepeat r k, ?_, ?_⟩
  · intro hnil
    have hge := v115WordRepeat_count_le_length r hr k
    have hlen := congrArg List.length hnil
    simp only [List.length_nil] at hlen
    omega
  · rw [v115FixedHom_wordRepeat H r k, hrt]

/--
A right-stationary positive element is idempotent in a locally trivial
positive-image semigroup.  A positive idempotent power of the
right-multiplier provides the needed ideal factor.
-/
theorem v115_positiveImage_stationary_idempotent
    (H : FixedFiniteMonoidHom α M)
    (hlocal : V115PositiveImageLocallyTrivial H)
    {p t : M}
    (hp : V115InPositiveImage H p)
    (ht : V115InPositiveImage H t)
    (hpfix : p * t = p) :
    p * p = p := by
  obtain ⟨k, hk, hidem⟩ :=
    v115_exists_positive_idempotent_power t
  have htpos : V115InPositiveImage H (t ^ k) :=
    v115_positiveImage_pow H ht k hk
  have hfixpow : ∀ j : Nat, p * t ^ j = p := by
    intro j
    induction j with
    | zero =>
        simp
    | succ j ih =>
        calc
          p * t ^ (j + 1) = (p * t ^ j) * t := by
            rw [pow_succ, mul_assoc]
          _ = p * t := by rw [ih]
          _ = p := hpfix
  have hpe :=
    v115_positiveImage_idempotent_left
      H hlocal htpos hp hidem
  simpa only [hfixpow k] using hpe

end V115FinitePositivePowers
end TCS1
end LeanCfgProject
