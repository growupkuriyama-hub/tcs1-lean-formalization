import LeanCfgProject.TCS1.V119GapFiniteSSBNF

/-!
# TCS #1 v119: exact finite source E_i language and typed gap

Every finite SSBNF E_i derivation is shown to belong to the abstract
E_i derivation relation, which was already machine-checked in the v117
core. The converse was established in V119GapFiniteSSBNF.

Thus the actual finite grammar has exactly one type-one E_i yield,
the all-a word of length 2^i, and (E_n,one) is an active typed symbol.
This module is not by itself the source reduction and O(n) rule-count
certificate.
-/

namespace LeanCfgProject
namespace TCS1

theorem v119Gap_sourceE_to_core
    (n : Nat)
    {A : V119GapNT n}
    {w : Word V117GapLetter}
    (d : UntypedDerives
      (v119GapTerminal n) (v119GapBinary n) A w) :
    ∀ (i : Fin (n + 1)), A = .e i →
      V117GapEDerives i.val w := by
  induction d with
  | @terminal A a hterm =>
      intro i hA
      subst A
      cases a with
      | a =>
          change i.val = 0 at hterm
          rw [hterm]
          exact V117GapEDerives.base
      | c =>
          change i.val ≠ 0 at hterm
          have hsucc : i.val = (i.val - 1) + 1 := by omega
          rw [hsucc]
          exact V117GapEDerives.shortcut
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      intro i hA
      subst A
      cases B with
      | u =>
          cases C <;> simp [v119GapBinary] at hbin
      | d =>
          cases C <;> simp [v119GapBinary] at hbin
      | e j =>
          cases C with
          | u => simp [v119GapBinary] at hbin
          | d => simp [v119GapBinary] at hbin
          | e k =>
              change i.val = j.val + 1 ∧
                j.val = k.val at hbin
              have hjk : j = k := Fin.ext hbin.2
              subst k
              rw [hbin.1]
              exact V117GapEDerives.branch
                (ihB j rfl) (ihC j rfl)

theorem v119Gap_sourceE_iff_core
    (n : Nat)
    (i : Fin (n + 1))
    (w : Word V117GapLetter) :
    UntypedDerives (v119GapTerminal n) (v119GapBinary n)
      (.e i) w ↔ V117GapEDerives i.val w := by
  constructor
  · intro d
    exact v119Gap_sourceE_to_core n d i rfl
  · intro d
    simpa using
      (v119GapEDerives_to_source d n (by omega : i.val ≤ n))

theorem v119Gap_typedE_one_exact
    (n : Nat)
    (i : Fin (n + 1))
    {w : Word V117GapLetter}
    (d : TypedDerives
      v117GapHom (v119GapTerminal n) (v119GapBinary n)
      (.e i, (1 : V117GapType)) w) :
    w = List.replicate (2 ^ i.val) .a := by
  have dSource :
      UntypedDerives (v119GapTerminal n) (v119GapBinary n)
        (.e i) w :=
    typedDerives_erase v117GapHom
      (v119GapTerminal n) (v119GapBinary n) d
  have dCore : V117GapEDerives i.val w :=
    (v119Gap_sourceE_iff_core n i w).mp dSource
  have ht : v117GapHom.h w = (1 : V117GapType) :=
    typedDerives_yield_type v117GapHom
      (v119GapTerminal n) (v119GapBinary n) d
  exact v117GapEDerives_type_one_exact dCore ht

/--
The actual finite (E_n,1) is retained by the typed trim and each of
its complete type-one yields has length exactly 2^n.
-/
theorem v119Gap_En_active_and_exponential
    (n : Nat) :
    ConcreteTypedActive v117GapHom
      (v119GapTerminal n) (v119GapBinary n) (v119GapStart n)
      ((.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))),
       (1 : V117GapType)) ∧
    (∀ (w : Word V117GapLetter),
      TypedDerives v117GapHom
        (v119GapTerminal n) (v119GapBinary n)
        ((.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))),
         (1 : V117GapType)) w →
      w.length = 2 ^ n) := by
  constructor
  · exact v119Gap_En_one_survives_trim n
  · intro w d
    have he :=
      v119Gap_typedE_one_exact n
        (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) d
    rw [he]
    simp

end TCS1
end LeanCfgProject
