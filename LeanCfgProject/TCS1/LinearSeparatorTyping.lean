import LeanCfgProject.TCS1.LinearSeparatorExample

/-!
# TCS #1 v77: the four-element typing for L_{±,e}

This module formalizes the concrete monoid M_{±,e} from Section 8.1.
It is the identity adjoined to a three-element null semigroup:
1, kappa_cd, kappa_e, 0.

The associated homomorphism maps a,b to 1, c,d to kappa_cd, and e to
kappa_e.
-/

namespace LeanCfgProject
namespace TCS1

inductive LpmType where
  | one
  | cd
  | ee
  | zero
  deriving DecidableEq, Fintype, Repr

namespace LpmType

def mul : LpmType → LpmType → LpmType
  | one, y => y
  | x, one => x
  | _, _ => zero

instance : Monoid LpmType where
  one := one
  mul := mul
  one_mul x := by
    cases x <;> rfl
  mul_one x := by
    cases x <;> rfl
  mul_assoc x y z := by
    cases x <;> cases y <;> cases z <;> rfl

/-- Multiplying a center type on the left can never return the identity. -/
theorem cd_mul_ne_one (t : LpmType) :
    cd * t ≠ 1 := by
  cases t <;> decide

/-- The e-center type likewise never returns the identity on the left. -/
theorem ee_mul_ne_one (t : LpmType) :
    ee * t ≠ 1 := by
  cases t <;> decide

end LpmType

open LpmSymbol LpmType

def lpmLetterType : LpmSymbol → LpmType
  | a => 1
  | b => 1
  | c => cd
  | d => cd
  | e => ee

/-- The four-element monoid homomorphism h from equation (8.1). -/
def lpmTyping :
    FixedFiniteMonoidHom LpmSymbol LpmType where
  h w := (w.map lpmLetterType).prod
  map_nil := by simp
  map_append u v := by
    simp [List.map_append, List.prod_append]

@[simp] theorem lpmTyping_a :
    lpmTyping.h [a] = 1 := by
  rfl

@[simp] theorem lpmTyping_b :
    lpmTyping.h [b] = 1 := by
  rfl

@[simp] theorem lpmTyping_c :
    lpmTyping.h [c] = cd := by
  rfl

@[simp] theorem lpmTyping_d :
    lpmTyping.h [d] = cd := by
  rfl

@[simp] theorem lpmTyping_e :
    lpmTyping.h [e] = ee := by
  rfl

@[simp] theorem lpmTyping_replicate_a
    (n : Nat) :
    lpmTyping.h (List.replicate n a) = 1 := by
  simp [lpmTyping, lpmLetterType]

@[simp] theorem lpmTyping_replicate_b
    (n : Nat) :
    lpmTyping.h (List.replicate n b) = 1 := by
  simp [lpmTyping, lpmLetterType]

/-- The type of a canonical one-center word is exactly the type of its center. -/
@[simp] theorem lpmTyping_core
    (n : Nat) (z : LpmSymbol) :
    lpmTyping.h (lpmCore n z) =
      lpmLetterType z := by
  simp [lpmCore, lpmTyping, lpmLetterType,
    List.map_append, List.prod_append]

@[simp] theorem lpmTyping_core_c
    (n : Nat) :
    lpmTyping.h (lpmCore n c) = cd := by
  simp [lpmLetterType]

@[simp] theorem lpmTyping_core_d
    (n : Nat) :
    lpmTyping.h (lpmCore n d) = cd := by
  simp [lpmLetterType]

@[simp] theorem lpmTyping_core_e
    (n : Nat) :
    lpmTyping.h (lpmCore n e) = ee := by
  simp [lpmLetterType]

/-- One-step evaluation of the concrete separator typing. -/
@[simp] theorem lpmTyping_cons
    (z : LpmSymbol) (w : Word LpmSymbol) :
    lpmTyping.h (z :: w) =
      lpmLetterType z * lpmTyping.h w := by
  simp [lpmTyping]

/-- Boundary letters are exactly the letters typed by the identity. -/
def LpmBoundaryLetter (z : LpmSymbol) : Prop :=
  z = a ∨ z = b

/--
A word has h-type 1 exactly when it contains no center symbol.
This is the first case distinction in the manuscript's fixed-h proof.
-/
theorem lpmTyping_eq_one_iff_boundary_only
    (w : Word LpmSymbol) :
    lpmTyping.h w = 1 ↔
      ∀ z ∈ w, LpmBoundaryLetter z := by
  induction w with
  | nil =>
      simp [lpmTyping]
  | cons z w ih =>
      constructor
      · intro h
        have hzw :
            lpmLetterType z * lpmTyping.h w = 1 := by
          simpa using h
        have hz : LpmBoundaryLetter z := by
          cases z with
          | a => exact Or.inl rfl
          | b => exact Or.inr rfl
          | c =>
              exact False.elim
                (LpmType.cd_mul_ne_one
                  (lpmTyping.h w) hzw)
          | d =>
              exact False.elim
                (LpmType.cd_mul_ne_one
                  (lpmTyping.h w) hzw)
          | e =>
              exact False.elim
                (LpmType.ee_mul_ne_one
                  (lpmTyping.h w) hzw)
        have htail : lpmTyping.h w = 1 := by
          rcases hz with hza | hzb
          · subst z
            simpa [lpmLetterType] using hzw
          · subst z
            simpa [lpmLetterType] using hzw
        intro t ht
        rcases List.mem_cons.mp ht with htz | htw
        · subst t
          exact hz
        · exact (ih.mp htail) t htw
      · intro hall
        have hz : LpmBoundaryLetter z :=
          hall z (by simp)
        have htailBoundary :
            ∀ t ∈ w, LpmBoundaryLetter t := by
          intro t ht
          exact hall t (by simp [ht])
        have htail : lpmTyping.h w = 1 :=
          ih.mpr htailBoundary
        have hzw :
            lpmLetterType z * lpmTyping.h w = 1 := by
          rcases hz with hza | hzb
          · subst z
            simp [lpmLetterType, htail]
          · subst z
            simp [lpmLetterType, htail]
        simpa using hzw

end TCS1
end LeanCfgProject
