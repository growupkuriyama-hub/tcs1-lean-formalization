import LeanCfgProject.TCS1.FixedHSubstitutability

/-!
# TCS #1 v68: semantic contract for the fixed-window summary h_{k,l}

Proposition 3.2 of the v68 manuscript defines h_{k,l} by a tagged short/long
summary.  Short words (length < max(1,k+l)) are remembered exactly; long
words are remembered only through their length-k prefix and length-l suffix.

This module isolates the equality relation induced by that summary without yet
choosing a concrete finite monoid representation.  It is enough for the
Section 7 semantic argument:

* short summaries identify only the same word;
* for k+l>0, two words with the same explicit boundary decomposition
  p ++ middle ++ q have the same long summary;
* any monoid homomorphism that respects this summary satisfies the
  BoundaryTyping contract used by FixedWindowBoundarySemantic.

The remaining representation-level task is to instantiate this contract with
the concrete finite monoid M_{k,l} from Proposition 3.2.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FixedWindowSummarySemantic

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- The manuscript's short/long cutoff m0=max{1,k+l}. -/
def fixedWindowThreshold (k l : Nat) : Nat :=
  max 1 (k + l)

/--
Equality relation induced by the tagged h_{k,l} summary.

The second disjunct is stated through a common explicit prefix/suffix
decomposition rather than List.take/takeRight.  For long words this is exactly
what the marked-boundary argument in Lemma 7.1 produces.
-/
def SameFixedWindowSummary
    (k l : Nat)
    (x y : Word α) : Prop :=
  (x.length < fixedWindowThreshold k l ∧ y = x)
  ∨
  (fixedWindowThreshold k l ≤ x.length ∧
   fixedWindowThreshold k l ≤ y.length ∧
   ∃ p q m₁ m₂ : Word α,
     p.length = k ∧
     q.length = l ∧
     x = p ++ m₁ ++ q ∧
     y = p ++ m₂ ++ q)

/--
A fixed finite-monoid typing respects the window summary when summary equality
implies equality of monoid types.
-/
def RespectsFixedWindowSummary
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat) : Prop :=
  ∀ x y : Word α,
    SameFixedWindowSummary k l x y →
    H.h x = H.h y

/--
Conversely, a typing reflects the fixed-window summary when equality of types
forces equality of the tagged short/long summary.  The concrete h_{k,l} of
Proposition 3.2 satisfies both directions.
-/
def ReflectsFixedWindowSummary
    (H : FixedFiniteMonoidHom α M)
    (k l : Nat) : Prop :=
  ∀ x y : Word α,
    H.h x = H.h y →
    SameFixedWindowSummary k l x y

/-- Short-summary equality remembers the short word exactly. -/
theorem sameFixedWindowSummary_short_left_eq
    {k l : Nat}
    {x y : Word α}
    (hx : x.length < fixedWindowThreshold k l)
    (hsame : SameFixedWindowSummary k l x y) :
    y = x := by
  rcases hsame with hshort | hlong
  · exact hshort.2
  · have hcontra :
        fixedWindowThreshold k l ≤ x.length :=
      hlong.1
    omega

/--
Hence, under a summary-reflecting typing, a short reference word is the unique
word of its type.  This is the short-word branch of Lemma 7.1.
-/
theorem short_word_unique_of_type
    (H : FixedFiniteMonoidHom α M)
    {k l : Nat}
    (hreflect : ReflectsFixedWindowSummary H k l)
    {x y : Word α}
    (hx : x.length < fixedWindowThreshold k l)
    (htype : H.h x = H.h y) :
    y = x := by
  exact
    sameFixedWindowSummary_short_left_eq
      hx (hreflect x y htype)

/-- At the (0,0) window, any two nonempty words have the same summary. -/
theorem zero_words_sameFixedWindowSummary
    {x y : Word α}
    (hx : 0 < x.length)
    (hy : 0 < y.length) :
    SameFixedWindowSummary 0 0 x y := by
  right
  refine ⟨?_, ?_, [], [], x, y, by simp, by simp, ?_, ?_⟩
  · simp [fixedWindowThreshold]
    exact hx
  · simp [fixedWindowThreshold]
    exact hy
  · simp
  · simp

/--
Hence any typing that respects the (0,0) fixed-window summary is constant on
the nonempty words, exactly as used in the r=0 branch of Lemma 7.1.
-/
theorem zero_type_eq_of_respectsFixedWindowSummary
    (H : FixedFiniteMonoidHom α M)
    (hrespect : RespectsFixedWindowSummary H 0 0)
    {x y : Word α}
    (hx : 0 < x.length)
    (hy : 0 < y.length) :
    H.h x = H.h y := by
  exact
    hrespect x y
      (zero_words_sameFixedWindowSummary hx hy)

/--
When r=k+l is positive, the threshold max(1,r) is exactly r.
-/
theorem fixedWindowThreshold_eq_sum_of_pos
    {k l : Nat}
    (hr : 0 < k + l) :
    fixedWindowThreshold k l = k + l := by
  unfold fixedWindowThreshold
  exact Nat.max_eq_right (Nat.succ_le_iff.mpr hr)

/--
Two words assembled with the same length-k prefix and length-l suffix have the
same long fixed-window summary whenever k+l>0.
-/
theorem boundary_words_sameFixedWindowSummary
    {k l : Nat}
    (hr : 0 < k + l)
    (p q m₁ m₂ : Word α)
    (hp : p.length = k)
    (hq : q.length = l) :
    SameFixedWindowSummary k l
      (p ++ m₁ ++ q)
      (p ++ m₂ ++ q) := by
  have hcut :
      fixedWindowThreshold k l = k + l :=
    fixedWindowThreshold_eq_sum_of_pos hr
  have hx :
      fixedWindowThreshold k l ≤
        (p ++ m₁ ++ q).length := by
    rw [hcut]
    simp only [List.length_append]
    omega
  have hy :
      fixedWindowThreshold k l ≤
        (p ++ m₂ ++ q).length := by
    rw [hcut]
    simp only [List.length_append]
    omega
  exact Or.inr
    ⟨hx, hy,
      p, q, m₁, m₂,
      hp, hq, rfl, rfl⟩

/--
Paper-facing consequence: any typing that respects the h_{k,l} summary assigns
the same type to two words with the same marked boundary.
-/
theorem boundary_type_eq_of_respectsFixedWindowSummary
    (H : FixedFiniteMonoidHom α M)
    {k l : Nat}
    (hr : 0 < k + l)
    (hrespect : RespectsFixedWindowSummary H k l)
    (p q m₁ m₂ : Word α)
    (hp : p.length = k)
    (hq : q.length = l) :
    H.h (p ++ m₁ ++ q) =
      H.h (p ++ m₂ ++ q) := by
  exact
    hrespect
      (p ++ m₁ ++ q)
      (p ++ m₂ ++ q)
      (boundary_words_sameFixedWindowSummary
        hr p q m₁ m₂ hp hq)

end FixedWindowSummarySemantic

end TCS1
end LeanCfgProject
