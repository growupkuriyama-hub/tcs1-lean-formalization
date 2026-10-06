import LeanCfgProject.TCS1.V117TypedThicknessGapCore
import LeanCfgProject.TCS1.ConcreteTypedTrimming
import Mathlib.Tactic

/-!
# TCS #1 v119: a finite SSBNF presentation for the typed-thickness example

For each n, this defines the *finite* source non-start grammar U, D,
E_0 ... E_n, with start child U, and implements exactly the terminal and
binary rules in Proposition prop:typed-thickness-gap.

This stage proves:
* all source non-start symbols have a one-letter yield;
* U derives precisely all nonempty words;
* the abstract E_i derivations in V117TypedThicknessGapCore embed into
  the finite SSBNF, so E_n has the all-a yield of length 2^n;
* (E_n, 1) survives the exact productive/reachable typed trim, via
  S_0 -> U_zero -> (E_n)_one D_zero.

The converse identification of *all* finite E_i derivations with the
abstract E_i relation, source reducedness, and the exact source-size
bound are still separate obligations. This file alone is NOT the
full proposition certificate.
-/

namespace LeanCfgProject
namespace TCS1

/-- Finite non-start state family U, D, E_0,...,E_n. -/
inductive V119GapNT (n : Nat) where
  | u
  | d
  | e (i : Fin (n + 1))
  deriving DecidableEq, Fintype, Repr

/-- The separated start S_0 has the single start production S_0 -> U. -/
def v119GapStart (n : Nat) : V119GapNT n → Prop
  | .u => True
  | _ => False

/-- U -> a | c, D -> c, E_0 -> a, E_i -> c for positive i. -/
def v119GapTerminal (n : Nat) :
    V119GapNT n → V117GapLetter → Prop
  | .u, .a => True
  | .u, .c => True
  | .d, .c => True
  | .e i, .a => i.val = 0
  | .e i, .c => i.val ≠ 0
  | _, _ => False

/--
U -> U U | E_n D, and E_i -> E_(i-1) E_(i-1) for positive i.
The last conjunct in the E case rules out unequal children.
-/
def v119GapBinary (n : Nat) :
    V119GapNT n → V119GapNT n → V119GapNT n → Prop
  | .u, .u, .u => True
  | .u, .e i, .d => i.val = n
  | .e i, .e j, .e k =>
      i.val = j.val + 1 ∧ j.val = k.val
  | _, _, _ => False

/-- Every E_i abstract derivation is a derivation in the finite SSBNF. -/
theorem v119GapEDerives_to_source
    {i : Nat} {w : Word V117GapLetter}
    (d : V117GapEDerives i w) :
    ∀ (n : Nat) (hi : i ≤ n),
      UntypedDerives (v119GapTerminal n) (v119GapBinary n)
        (.e (⟨i, Nat.lt_succ_of_le hi⟩ : Fin (n + 1))) w := by
  induction d with
  | base =>
      intro n hi
      exact UntypedDerives.terminal (by simp [v119GapTerminal])
  | @shortcut j =>
      intro n hi
      exact UntypedDerives.terminal (by simp [v119GapTerminal])
  | @branch j u v dl dr ihl ihr =>
      intro n hi
      have hl : j ≤ n := by omega
      have hright : j ≤ n := by omega
      have hb :
          v119GapBinary n
            (.e (⟨j + 1, by omega⟩ : Fin (n + 1)))
            (.e (⟨j, by omega⟩ : Fin (n + 1)))
            (.e (⟨j, by omega⟩ : Fin (n + 1))) := by
        simp [v119GapBinary]
      exact UntypedDerives.binary hb (ihl n hl) (ihr n hright)

/-- U derives every positive word by U -> U U and the two terminal rules. -/
theorem v119Gap_u_derives_nonempty
    (n : Nat) (w : Word V117GapLetter) :
    w ≠ [] →
      UntypedDerives (v119GapTerminal n) (v119GapBinary n)
        .u w := by
  induction w with
  | nil =>
      intro h
      exact False.elim (h rfl)
  | cons a rest ih =>
      intro _
      cases rest with
      | nil =>
          cases a with
          | a => exact UntypedDerives.terminal (by simp [v119GapTerminal])
          | c => exact UntypedDerives.terminal (by simp [v119GapTerminal])
      | cons b tail =>
          have hl :
              UntypedDerives (v119GapTerminal n) (v119GapBinary n)
                .u [a] := by
            cases a <;> exact UntypedDerives.terminal
              (by simp [v119GapTerminal])
          have hr :
              UntypedDerives (v119GapTerminal n) (v119GapBinary n)
                .u (b :: tail) := ih (by simp)
          have d :
              UntypedDerives (v119GapTerminal n) (v119GapBinary n)
                .u ([a] ++ (b :: tail)) :=
            UntypedDerives.binary (by simp [v119GapBinary]) hl hr
          simpa using d

/-- U's language is exactly the target {a,c}^+, independent of n. -/
theorem v119Gap_u_derives_iff_nonempty
    (n : Nat) (w : Word V117GapLetter) :
    UntypedDerives (v119GapTerminal n) (v119GapBinary n)
      .u w ↔ w ≠ [] := by
  constructor
  · intro d hnil
    have hp :=
      untypedDerives_length_pos
        (v119GapTerminal n) (v119GapBinary n) d
    simp [hnil] at hp
  · exact v119Gap_u_derives_nonempty n w

/-- All non-start source symbols have a terminal yield of length one. -/
theorem v119Gap_all_source_short_yields (n : Nat) :
    ∀ A : V119GapNT n,
      ∃ w : Word V117GapLetter,
        UntypedDerives (v119GapTerminal n) (v119GapBinary n)
          A w ∧ w.length = 1 := by
  intro A
  cases A with
  | u =>
      exact ⟨[.a],
        UntypedDerives.terminal (by simp [v119GapTerminal]), rfl⟩
  | d =>
      exact ⟨[.c],
        UntypedDerives.terminal (by simp [v119GapTerminal]), rfl⟩
  | e i =>
      by_cases hzero : i.val = 0
      · exact ⟨[.a],
          UntypedDerives.terminal (by simp [v119GapTerminal, hzero]), rfl⟩
      · exact ⟨[.c],
          UntypedDerives.terminal (by simp [v119GapTerminal, hzero]), rfl⟩

/-- The root E_n derives the exponentially long, c-free word. -/
theorem v119Gap_En_source_all_a (n : Nat) :
    UntypedDerives (v119GapTerminal n) (v119GapBinary n)
      (.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)))
      (List.replicate (2 ^ n) .a) :=
  v119GapEDerives_to_source (v117GapEDerives_all_a n)
    n (Nat.le_refl n)

/--
The type-one E_n symbol is still reachable after productive-then-reachable
typed refinement; it is a left child of the successful typed U -> E_n D.
-/
theorem v119Gap_En_one_survives_trim (n : Nat) :
    ConcreteTypedActive v117GapHom
      (v119GapTerminal n) (v119GapBinary n) (v119GapStart n)
      ((.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))),
        (1 : V117GapType)) := by
  let en : V119GapNT n :=
    .e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))
  let wa : Word V117GapLetter := List.replicate (2 ^ n) .a
  have hword : v117GapHom.h wa = 1 := by
    apply (v117GapWordType_one_iff _).2
    simp [wa]
  have deSource :
      UntypedDerives (v119GapTerminal n) (v119GapBinary n)
        en wa := v119Gap_En_source_all_a n
  have de :
      TypedDerives v117GapHom
        (v119GapTerminal n) (v119GapBinary n)
        (en, (1 : V117GapType)) wa := by
    have d := untypedDerives_lift v117GapHom
      (v119GapTerminal n) (v119GapBinary n) deSource
    rw [hword] at d
    exact d
  have dd :
      TypedDerives v117GapHom
        (v119GapTerminal n) (v119GapBinary n)
        (.d, v117GapHom.h [.c]) [.c] :=
    TypedDerives.terminal (by simp [v119GapTerminal])
  have hbin :
      v119GapBinary n .u en .d := by
    simp [v119GapBinary, en]
  have du :
      TypedDerives v117GapHom
        (v119GapTerminal n) (v119GapBinary n)
        (.u, (1 : V117GapType) * v117GapHom.h [.c])
        (wa ++ [.c]) :=
    TypedDerives.binary hbin de dd
  have hparent :
      ConcreteTypedActive v117GapHom
        (v119GapTerminal n) (v119GapBinary n) (v119GapStart n)
        (.u, (1 : V117GapType) * v117GapHom.h [.c]) :=
    ProductiveTypedReachable.start
      (by simp [v119GapStart])
      ⟨wa ++ [.c], du⟩
  exact ProductiveTypedReachable.left hparent hbin
    ⟨wa, de⟩ ⟨[.c], dd⟩

end TCS1
end LeanCfgProject
