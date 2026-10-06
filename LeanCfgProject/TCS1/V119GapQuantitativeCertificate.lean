import LeanCfgProject.TCS1.V119GapRuleIndex
import LeanCfgProject.TCS1.WitnessSetConstruction

/-!
# TCS #1 v119: assembled source-to-typed thickness gap

The exact finite source grammar has n+3 non-start symbols and an exhaustive
finite production index of size 2n+7. All source states are genuinely
reachable and have length-one yields. The type-one E_n state is active
after the productive/reachable refinement, but every reduced typed yield of
that active state has length exactly 2^n.

Thus the canonical productive word *under any* reduced witness system
has length 2^n. This is the source-exact content behind the inequality
tau_h^typ(G_n^c) >= 2^n. It is not an algorithm-independent lower bound
on positive characteristic data.
-/

namespace LeanCfgProject
namespace TCS1

/-- No trimming step can shorten the E_n type-one word. -/
theorem v119Gap_trimmed_En_one_length
    (n : Nat)
    {w : Word V117GapLetter}
    (d :
      ReducedTypedDerives
        v117GapHom
        (v119GapTerminal n) (v119GapBinary n)
        (ConcreteTypedActive
          v117GapHom
          (v119GapTerminal n) (v119GapBinary n) (v119GapStart n))
        ((.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))),
          (1 : V117GapType)) w) :
    w.length = 2 ^ n := by
  have df :=
    reducedTypedDerives_to_typedDerives
      v117GapHom
      (v119GapTerminal n) (v119GapBinary n)
      (ConcreteTypedActive
        v117GapHom
        (v119GapTerminal n) (v119GapBinary n) (v119GapStart n))
      d
  exact (v119Gap_En_active_and_exponential n).2 w df

/-- Every allowed choice of canonical typed yields has the same gap. -/
theorem v119Gap_any_canonical_En_one_length
    (n : Nat)
    (C :
      ReducedWitnessChoices
        v117GapHom
        (v119GapTerminal n) (v119GapBinary n)
        (v119GapStart n) False
        (ConcreteTypedActive
          v117GapHom
          (v119GapTerminal n) (v119GapBinary n) (v119GapStart n))) :
    (C.omega
      ((.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))),
       (1 : V117GapType))).length = 2 ^ n := by
  have hactive :=
    (v119Gap_En_active_and_exponential n).1
  exact v119Gap_trimmed_En_one_length n
    (C.omegaDerives _ hactive)

/--
The paper-facing finite representation and typed gap, in one conjunction.
The finite source representation has O(n) rules/states and thickness 1;
every witness-choice interface for its active typed refinement has an
exponentially long E_n one-typed yield.
-/
theorem v119Gap_source_to_typed_certificate (n : Nat) :
    Fintype.card (V119GapNT n) = n + 3 ∧
    Fintype.card (V119GapRuleCode n) = 2 * n + 7 ∧
    (∀ A : V119GapNT n,
      V119GapSourceReachable n A ∧
      ∃ w : Word V117GapLetter,
        UntypedDerives
          (v119GapTerminal n) (v119GapBinary n)
          A w ∧ w.length = 1) ∧
    ConcreteTypedActive v117GapHom
      (v119GapTerminal n) (v119GapBinary n) (v119GapStart n)
      ((.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))),
       (1 : V117GapType)) ∧
    (∀ (C :
      ReducedWitnessChoices
        v117GapHom
        (v119GapTerminal n) (v119GapBinary n)
        (v119GapStart n) False
        (ConcreteTypedActive
          v117GapHom
          (v119GapTerminal n) (v119GapBinary n) (v119GapStart n))),
      (C.omega
        ((.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))),
         (1 : V117GapType))).length = 2 ^ n) := by
  refine ⟨v119GapNT_card n, v119GapRuleCode_card n,
    v119Gap_source_reduced_certificate n,
    (v119Gap_En_active_and_exponential n).1, ?_⟩
  intro C
  exact v119Gap_any_canonical_En_one_length n C

end TCS1
end LeanCfgProject
