import LeanCfgProject.TCS1.ExecutableConservativeLearner
import LeanCfgProject.TCS1.ReconstructionProductionTables

/-!
# TCS #1 v79: executable reconstruction smoke test

The theorem-facing development proves that the factor-slot CYK parser and the
conservative learner are computable definitions.  This file adds a tiny closed
instance evaluated by Lean itself.

The alphabet is Bool and the fixed monoid is a one-element monoid.  From the
sample {[true]}, the parser accepts [true], rejects [false] and epsilon, and
the conservative update therefore keeps its current hypothesis on [true] but
rebuilds when [false] arrives.

These are deliberately small regression tests: they exercise the same
factor-slot enumeration, finite R2/R3 closure, CYK chart, and keep/rebuild
branch used by the general executable definitions.
-/

namespace LeanCfgProject
namespace TCS1

namespace ExecutableSmokeTest

inductive OneMonoid
  | star
deriving DecidableEq, Fintype, Repr

instance : Monoid OneMonoid where
  one := OneMonoid.star
  mul _ _ := OneMonoid.star
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl

def smokeTyping : FixedFiniteMonoidHom Bool OneMonoid where
  h _ := OneMonoid.star
  map_nil := rfl
  map_append _ _ := rfl

def smokeSample : Finset (Word Bool) :=
  { [true] }

def smokeAccumulated : Finset (Word Bool) :=
  { [true], [false] }

theorem smoke_member_true :
    reconstructionFactorSlotCYKMember
        smokeTyping smokeSample [true]
      =
    true := by
  native_decide

theorem smoke_reject_false :
    reconstructionFactorSlotCYKMember
        smokeTyping smokeSample [false]
      =
    false := by
  native_decide

theorem smoke_reject_epsilon :
    reconstructionFactorSlotCYKMember
        smokeTyping smokeSample []
      =
    false := by
  native_decide

theorem smoke_update_keeps_generated_word :
    executableConservativeUpdate
        smokeTyping smokeSample smokeAccumulated [true]
      =
    smokeSample := by
  native_decide

theorem smoke_update_rebuilds_on_missing_word :
    executableConservativeUpdate
        smokeTyping smokeSample smokeAccumulated [false]
      =
    smokeAccumulated := by
  native_decide


theorem smoke_materialized_member_true :
    reconstructionMaterializedCYKMember
        smokeTyping smokeSample [true]
      =
    true := by
  native_decide

theorem smoke_materialized_reject_false :
    reconstructionMaterializedCYKMember
        smokeTyping smokeSample [false]
      =
    false := by
  native_decide

end ExecutableSmokeTest

end TCS1
end LeanCfgProject
