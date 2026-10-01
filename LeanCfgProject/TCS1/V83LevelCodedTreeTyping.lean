import LeanCfgProject.TCS1.V83LevelCodedTreeSyntax
import LeanCfgProject.TCS1.ClarkEyraudSpecialCase
import LeanCfgProject.TCS1.FixedHTypeFiberRestriction

/-!
# TCS #1 v83: two-element typing for the level-coded lower bound

The current manuscript uses the two-element monoid {1,zeta}, with zeta
absorbing, and maps exactly the letter c to zeta.  This file formalizes that
typing and proves that the shortcut-containing tree language is precisely the
zeta-fibre restriction of the full level-coded language.
-/

namespace LeanCfgProject
namespace TCS1

inductive LevelTreeType where
  | one
  | zeta
  deriving DecidableEq, Fintype, Repr

namespace LevelTreeType

def mul : LevelTreeType → LevelTreeType → LevelTreeType
  | one, y => y
  | zeta, _ => zeta

instance : Monoid LevelTreeType where
  one := one
  mul := mul
  one_mul x := by
    cases x <;> rfl
  mul_one x := by
    cases x <;> rfl
  mul_assoc x y z := by
    cases x <;> cases y <;> cases z <;> rfl

@[simp] theorem one_mul_def (x : LevelTreeType) :
    one * x = x := by
  rfl

@[simp] theorem zeta_mul_def (x : LevelTreeType) :
    zeta * x = zeta := by
  rfl

end LevelTreeType

open LevelTreeType LevelTreeSymbol

def levelTreeLetterType : LevelTreeSymbol → LevelTreeType
  | c => zeta
  | _ => one

/-- The fixed two-element homomorphism h_circ from the lower-bound theorem. -/
def levelTreeTyping :
    FixedFiniteMonoidHom LevelTreeSymbol LevelTreeType where
  h w := (w.map levelTreeLetterType).prod
  map_nil := by simp
  map_append u v := by
    simp [List.map_append, List.prod_append]

@[simp] theorem levelTreeTyping_cons
    (x : LevelTreeSymbol)
    (xs : Word LevelTreeSymbol) :
    levelTreeTyping.h (x :: xs) =
      levelTreeLetterType x * levelTreeTyping.h xs := by
  rfl

/-- The typing evaluates to zeta exactly when c occurs. -/
theorem levelTreeTyping_eq_zeta_iff
    (w : Word LevelTreeSymbol) :
    levelTreeTyping.h w = zeta ↔ c ∈ w := by
  induction w with
  | nil =>
      simp [levelTreeTyping]
  | cons x xs ih =>
      simp only [levelTreeTyping_cons, List.mem_cons]
      cases x <;>
        simp [levelTreeLetterType, LevelTreeType.mul, ih]

/-- Equivalently, type one means c-free. -/
theorem levelTreeTyping_eq_one_iff
    (w : Word LevelTreeSymbol) :
    levelTreeTyping.h w = one ↔ c ∉ w := by
  constructor
  · intro hOne hc
    have hZ :
        levelTreeTyping.h w = zeta :=
      (levelTreeTyping_eq_zeta_iff w).2 hc
    rw [hOne] at hZ
    cases hZ
  · intro hc
    have hnotz : levelTreeTyping.h w ≠ zeta := by
      intro hz
      exact hc ((levelTreeTyping_eq_zeta_iff w).1 hz)
    cases hval : levelTreeTyping.h w with
    | one =>
        simpa using hval
    | zeta =>
        have hz : levelTreeTyping.h w = zeta := by
          simpa using hval
        exact False.elim (hnotz hz)

/--
The shortcut-containing language is exactly the zeta fibre of the full
level-coded language.
-/
theorem levelTreeShortcutLanguage_eq_fibre
    (n : Nat) :
    LevelTreeShortcutLanguage n =
      LevelTreeLanguage n ∩
        RecognizedPreimage levelTreeTyping
          ({zeta} : Set LevelTreeType) := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨hLang, hc⟩
    refine ⟨hLang, ?_⟩
    change levelTreeTyping.h w ∈ ({zeta} : Set LevelTreeType)
    simpa using (levelTreeTyping_eq_zeta_iff w).2 hc
  · rintro ⟨hLang, hType⟩
    refine ⟨hLang, ?_⟩
    change levelTreeTyping.h w ∈ ({zeta} : Set LevelTreeType) at hType
    have hz : levelTreeTyping.h w = zeta := by
      simpa using hType
    exact (levelTreeTyping_eq_zeta_iff w).1 hz

/--
Once Clark--Eyraud substitutability of T_n is established, both T_n and its
shortcut-containing sublanguage are fixed-h substitutable for the concrete
two-element typing.
-/
theorem levelTree_fixedH_package_of_clarkEyraud
    (n : Nat)
    (hce : ClarkEyraudSubstitutableOn (LevelTreeLanguage n)) :
    FixedHSubstitutable levelTreeTyping (LevelTreeLanguage n) ∧
      FixedHSubstitutable levelTreeTyping (LevelTreeShortcutLanguage n) := by
  have hfull :
      FixedHSubstitutable levelTreeTyping (LevelTreeLanguage n) :=
    fixedHSubstitutable_of_clarkEyraud levelTreeTyping hce
  constructor
  · exact hfull
  · rw [levelTreeShortcutLanguage_eq_fibre n]
    exact
      fixedHSubstitutable_inter_recognizedPreimage
        levelTreeTyping ({zeta} : Set LevelTreeType) hfull

end TCS1
end LeanCfgProject
