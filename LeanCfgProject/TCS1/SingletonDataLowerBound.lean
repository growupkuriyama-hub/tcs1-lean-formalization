import LeanCfgProject.TCS1.TrivialTargetEndpoints
import LeanCfgProject.TCS1.ReconstructionComplexityCounts

/-!
# TCS #1 v79: singleton characteristic-data lower bound

Section 6 explains why no characteristic-data bound depending only on the
size of an arbitrary CFG presentation can hold.  The semantic core of that
example is representation-independent:

* every singleton language is fixed-h substitutable for every fixed typing;
* every positive characteristic sample for a singleton must contain its
  unique word.

This module formalizes that core and specializes it to the exponentially long
word a^(2^n).  The separate small doubling-CFG presentation is handled at the
representation layer.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section SingletonDataLowerBound

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/--
Every singleton language is fixed-h substitutable for every fixed finite
monoid typing.

If two factors occur in the same context inside the unique target word, free
monoid cancellation forces the factors themselves to be equal.
-/
theorem singleton_fixedHSubstitutable
    (H : FixedFiniteMonoidHom α M)
    (word : Word α) :
    FixedHSubstitutable H ({word} : Set (Word α)) := by
  intro x y hx hy htype hshared
  rcases hshared with ⟨u, v, hxmem, hymem⟩
  have hxw : u ++ x ++ v = word := by
    simpa using hxmem
  have hyw : u ++ y ++ v = word := by
    simpa using hymem
  have hwhole :
      u ++ x ++ v = u ++ y ++ v :=
    hxw.trans hyw.symm
  have hpref : u ++ x = u ++ y :=
    List.append_cancel_right hwhole
  have hxy : x = y :=
    List.append_cancel_left hpref
  subst y
  rfl

/--
A positive characteristic sample for a singleton necessarily contains the
unique target word.
-/
theorem singleton_characteristic_sample_contains
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (word : Word α)
    (C : Finset (Word α))
    (hpositive :
      (↑C : Set (Word α)) ⊆
        ({word} : Set (Word α)))
    (hcharacteristic :
      BatchLanguage H C =
        ({word} : Set (Word α))) :
    word ∈ C := by
  by_contra hword
  have hCempty : C = ∅ := by
    ext z
    constructor
    · intro hz
      have hzword : z = word := by
        simpa using hpositive hz
      subst z
      exact False.elim (hword hz)
    · intro hz
      simp at hz
  have hwBatch :
      word ∈ BatchLanguage H C := by
    rw [hcharacteristic]
    simp
  rw [hCempty, batchLanguage_empty_eq H] at hwBatch
  exact hwBatch

/-- Every member contributes its own encoded length to the sample norm. -/
theorem member_encoding_le_reconstructionSampleNorm
    [DecidableEq α]
    (K : Finset (Word α))
    {word : Word α}
    (hword : word ∈ K) :
    word.length + 1 ≤ reconstructionSampleNorm K := by
  classical
  unfold reconstructionSampleNorm
  exact
    Finset.single_le_sum
      (fun z hz => Nat.zero_le (z.length + 1))
      hword

/--
Hence a positive characteristic sample for a singleton has encoded norm at
least the encoding length of the unique target word.
-/
theorem singleton_characteristic_sample_norm_ge
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (word : Word α)
    (C : Finset (Word α))
    (hpositive :
      (↑C : Set (Word α)) ⊆
        ({word} : Set (Word α)))
    (hcharacteristic :
      BatchLanguage H C =
        ({word} : Set (Word α))) :
    word.length + 1 ≤ reconstructionSampleNorm C := by
  exact
    member_encoding_le_reconstructionSampleNorm
      C
      (singleton_characteristic_sample_contains
        H word C hpositive hcharacteristic)

/-- The exponentially long unary word used by the Section 6 obstruction. -/
def doublingWord
    (a : α)
    (n : Nat) :
    Word α :=
  List.replicate (2 ^ n) a

@[simp] theorem doublingWord_length
    (a : α)
    (n : Nat) :
    (doublingWord a n).length = 2 ^ n := by
  simp [doublingWord]

/--
Every positive characteristic sample for the singleton {a^(2^n)} contains
that exponentially long word.
-/
theorem singleton_doubling_characteristic_contains
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (a : α)
    (n : Nat)
    (C : Finset (Word α))
    (hpositive :
      (↑C : Set (Word α)) ⊆
        ({doublingWord a n} : Set (Word α)))
    (hcharacteristic :
      BatchLanguage H C =
        ({doublingWord a n} : Set (Word α))) :
    doublingWord a n ∈ C :=
  singleton_characteristic_sample_contains
    H (doublingWord a n) C
    hpositive hcharacteristic

/--
Consequently its encoded characteristic-sample norm is at least 2^n + 1.
-/
theorem singleton_doubling_characteristic_norm_ge
    [DecidableEq α]
    (H : FixedFiniteMonoidHom α M)
    (a : α)
    (n : Nat)
    (C : Finset (Word α))
    (hpositive :
      (↑C : Set (Word α)) ⊆
        ({doublingWord a n} : Set (Word α)))
    (hcharacteristic :
      BatchLanguage H C =
        ({doublingWord a n} : Set (Word α))) :
    2 ^ n + 1 ≤ reconstructionSampleNorm C := by
  simpa using
    (singleton_characteristic_sample_norm_ge
      H (doublingWord a n) C
      hpositive hcharacteristic)

end SingletonDataLowerBound

end TCS1
end LeanCfgProject
