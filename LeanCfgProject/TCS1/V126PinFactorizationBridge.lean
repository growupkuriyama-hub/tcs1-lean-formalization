import LeanCfgProject.TCS1.V126NonLocalTrivialWindowObstruction
import LeanCfgProject.TCS1.V126LocallyTrivialCore
import LeanCfgProject.TCS1.V121LocallyTrivialBridge
import Mathlib.Tactic

/-!
# TCS #1 v126: exact bridge from Pin's finite-semigroup factorization

The manuscript uses the classical finite-semigroup input

  S^n = S E(S) S,  n = |S|+1,

for S = h(Sigma+).  This module isolates that external result as a precise
factorization contract and verifies every paper-specific step after it:

* positive image is closed under multiplication;
* local triviality on the positive image implies e t f = e f for positive
  idempotents e,f and positive t;
* the Pin factorization of the common n-prefix and n-suffix makes the H-value
  of p r q independent of the middle r;
* consequently the (n,n) fixed-window kernel refines H on positive words.

No project axiom is introduced.  The factorization contract is a theorem
hypothesis, corresponding exactly to the cited Pin result.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section V126PinFactorizationBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Positive image is multiplicatively closed. -/
theorem positiveImage_mul
    (H : FixedFiniteMonoidHom α M)
    {x y : M}
    (hx : PositiveImage H x)
    (hy : PositiveImage H y) :
    PositiveImage H (x * y) := by
  rcases hx with ⟨u, hune, hu⟩
  rcases hy with ⟨v, hvne, hv⟩
  refine ⟨u ++ v, ?_, ?_⟩
  · exact append_ne_nil_of_left_ne_nil hune
  · rw [H.map_append, hu, hv]

/-- Multiplying an arbitrary H-value between two positive-image elements still
lies in the positive image. -/
theorem positiveImage_mul_eval_mul
    (H : FixedFiniteMonoidHom α M)
    {b c : M}
    (hb : PositiveImage H b)
    (hc : PositiveImage H c)
    (r : Word α) :
    PositiveImage H (b * H.h r * c) := by
  rcases hb with ⟨u, hune, hu⟩
  rcases hc with ⟨v, hvne, hv⟩
  refine ⟨u ++ r ++ v, ?_, ?_⟩
  · have hur : u ++ r ≠ [] :=
      append_ne_nil_of_left_ne_nil hune
    exact append_ne_nil_of_left_ne_nil hur
  · rw [H.map_append, H.map_append, hu, hv]

/-- Positive-image version of the elementary locally-trivial sandwich identity. -/
theorem positiveLocallyTrivial_between_idempotents
    (H : FixedFiniteMonoidHom α M)
    (hlt : PositiveImageLocallyTrivial H)
    {e f t : M}
    (hepos : PositiveImage H e)
    (hfpos : PositiveImage H f)
    (htpos : PositiveImage H t)
    (he : e * e = e)
    (hf : f * f = f) :
    e * t * f = e * f := by
  have hfef : f * e * f = f :=
    hlt f hfpos hf e hepos
  have htfpos : PositiveImage H (t * f) :=
    positiveImage_mul H htpos hfpos
  have hete : e * (t * f) * e = e :=
    hlt e hepos he (t * f) htfpos
  calc
    e * t * f = e * t * (f * e * f) := by rw [hfef]
    _ = (e * (t * f) * e) * f := by simp only [mul_assoc]
    _ = e * f := by rw [hete]

/-- Exact word-level form of S^n = S E(S) S used by the manuscript.
For every word p of length n, H(p) factors as a e b with all three factors in
the positive image and e idempotent. -/
def PositiveLengthFactorization
    (H : FixedFiniteMonoidHom α M)
    (n : Nat) : Prop :=
  ∀ p : Word α,
    p.length = n →
    ∃ a e b : M,
      PositiveImage H a ∧
      PositiveImage H e ∧
      PositiveImage H b ∧
      e * e = e ∧
      H.h p = a * e * b

/-- Under the Pin factorization contract and local triviality, H(p r q) is
independent of the middle r whenever p,q both have length n. -/
theorem eval_boundary_independent
    (H : FixedFiniteMonoidHom α M)
    (n : Nat)
    (hfac : PositiveLengthFactorization H n)
    (hlt : PositiveImageLocallyTrivial H)
    {p q r s : Word α}
    (hp : p.length = n)
    (hq : q.length = n) :
    H.h (p ++ r ++ q) =
      H.h (p ++ s ++ q) := by
  obtain ⟨a, e, b, hapos, hepos, hbpos, heidem, hpH⟩ :=
    hfac p hp
  obtain ⟨c, f, d, hcpos, hfpos, hdpos, hfidem, hqH⟩ :=
    hfac q hq
  have hmidR :
      e * (b * H.h r * c) * f = e * f :=
    positiveLocallyTrivial_between_idempotents
      H hlt hepos hfpos
      (positiveImage_mul_eval_mul H hbpos hcpos r)
      heidem hfidem
  have hmidS :
      e * (b * H.h s * c) * f = e * f :=
    positiveLocallyTrivial_between_idempotents
      H hlt hepos hfpos
      (positiveImage_mul_eval_mul H hbpos hcpos s)
      heidem hfidem
  calc
    H.h (p ++ r ++ q)
        = (a * e * b) * H.h r * (c * f * d) := by
            rw [H.map_append, H.map_append, hpH, hqH]
    _ = a * (e * (b * H.h r * c) * f) * d := by
          simp only [mul_assoc]
    _ = a * (e * f) * d := by rw [hmidR]
    _ = a * (e * (b * H.h s * c) * f) * d := by rw [hmidS]
    _ = (a * e * b) * H.h s * (c * f * d) := by
          simp only [mul_assoc]
    _ = H.h (p ++ s ++ q) := by
          rw [H.map_append, H.map_append, hpH, hqH]

/-- The exact paper-specific consequence of Pin's factorization:
the fixed (n,n) window kernel refines H on nonempty words. -/
theorem positiveWindowKernelRefines_of_factorization
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (n : Nat)
    (hfac : PositiveLengthFactorization H n)
    (hlt : PositiveImageLocallyTrivial H) :
    PositiveWindowKernelRefines H n n := by
  intro x y hxne hyne hwindow
  have hsame :
      SameFixedWindowSummary n n x y :=
    fixedWindowMonoidHom_reflects
      (α := α) n n x y hwindow
  rcases hsame with hshort | hlong
  · exact congrArg H.h hshort.2.symm
  · rcases hlong with
      ⟨hxlong, hylong, p, q, mx, my,
        hp, hq, hxshape, hyshape⟩
    rw [hxshape, hyshape]
    exact
      eval_boundary_independent
        H n hfac hlt hp hq

/-- Paper-facing forward direction, with the only external algebraic input
exposed as PositiveLengthFactorization. -/
theorem locallyTrivial_implies_nn_window_refinement
    [Fintype α]
    (H : FixedFiniteMonoidHom α M)
    (n : Nat)
    (hfac : PositiveLengthFactorization H n)
    (hlt : PositiveImageLocallyTrivial H) :
    ∃ k l : Nat,
      PositiveWindowKernelRefines H k l := by
  exact ⟨n, n,
    positiveWindowKernelRefines_of_factorization
      H n hfac hlt⟩

end V126PinFactorizationBridge

end TCS1
end LeanCfgProject
