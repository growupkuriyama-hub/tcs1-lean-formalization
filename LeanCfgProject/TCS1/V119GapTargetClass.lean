import LeanCfgProject.TCS1.V119GapFiniteSSBNF
import Mathlib.Tactic

/-!
# TCS #1 v119: exact positive target and substitutability

The compact source grammar G_n^c has language {a,c}^+ independently
of n. Since this is the set of all nonempty words, it is substitutable
under the fixed two-element typing h_c (indeed any fixed typing).

This makes explicit the source proposition's \`L(G_n^c) in C_cf(h_c)\`
obligation at the language-theoretic level. The finite CFG
representation is supplied by V119GapFiniteSSBNF and V119GapRuleIndex.
-/

namespace LeanCfgProject
namespace TCS1

def v119GapTarget (n : Nat) : Set (Word V117GapLetter) :=
  {w | UntypedDerives (v119GapTerminal n) (v119GapBinary n) .u w}

theorem v119GapTarget_eq_nonempty (n : Nat) :
    v119GapTarget n = {w : Word V117GapLetter | w ≠ []} := by
  ext w
  exact v119Gap_u_derives_iff_nonempty n w

/-- A context around a nonempty internal factor is nonempty. -/
private theorem v119Gap_nonempty_context
    (u x v : Word V117GapLetter)
    (hx : x ≠ []) :
    u ++ x ++ v ≠ [] := by
  intro heq
  have hxlen : 0 < x.length :=
    List.length_pos_of_ne_nil hx
  have hzero : (u ++ x ++ v).length = 0 :=
    congrArg List.length heq
  simp only [List.length_append, List.length_nil] at hzero
  omega

/-- A fixed positive-language target is h_c-substitutable. -/
theorem v119Gap_target_fixedH_substitutable (n : Nat) :
    FixedHSubstitutable v117GapHom (v119GapTarget n) := by
  intro x y hx hy _htype _hshared
  apply Set.ext
  intro ctx
  change
    (UntypedDerives
      (v119GapTerminal n) (v119GapBinary n)
        .u (ctx.1 ++ x ++ ctx.2)) ↔
    (UntypedDerives
      (v119GapTerminal n) (v119GapBinary n)
        .u (ctx.1 ++ y ++ ctx.2))
  rw [v119Gap_u_derives_iff_nonempty,
      v119Gap_u_derives_iff_nonempty]
  exact ⟨fun _ => v119Gap_nonempty_context _ _ _ hy,
    fun _ => v119Gap_nonempty_context _ _ _ hx⟩

end TCS1
end LeanCfgProject
