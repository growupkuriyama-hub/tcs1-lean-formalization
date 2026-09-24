import LeanCfgProject.TCS1.LinearSeparatorDisplayedGrammar
import LeanCfgProject.TCS1.PreparedLinearGrammarSemantics

/-!
# TCS #1 v78: displayed separator grammar as a prepared linear CFG

The bespoke derivation relation in LinearSeparatorDisplayedGrammar mirrors
the notation used in the paper.  This file additionally realizes the same
six non-start productions inside the repository's generic
PreparedLinearIndexedCFG infrastructure.  Since that representation permits
only terminal rules and rules u B v with exactly one nonterminal, this gives
a machine-checked linear-CFG witness for L_{±,e}.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

inductive LpmLinearProd where
  | evC
  | evWrap
  | oddD
  | oddWrap
  | eeE
  | eeWrap
  deriving DecidableEq, Fintype, Repr

/-- The six non-start rules displayed in Proposition 8.6. -/
def lpmPreparedLinearGrammar :
    PreparedLinearIndexedCFG
      LpmLinearNT LpmSymbol LpmLinearProd where
  lhs
    | .evC => .ev
    | .evWrap => .ev
    | .oddD => .odd
    | .oddWrap => .odd
    | .eeE => .ee
    | .eeWrap => .ee
  rhs
    | .evC =>
        .terminals c []
    | .evWrap =>
        .around [a] .odd [b] (by simp)
    | .oddD =>
        .terminals d []
    | .oddWrap =>
        .around [a] .ev [b] (by simp)
    | .eeE =>
        .terminals e []
    | .eeWrap =>
        .around [a] .ee [b] (by simp)

/-- Generic prepared derivations imply the paper-facing displayed derivations. -/
theorem lpmPreparedDerives_to_displayed
    {A : LpmLinearNT}
    {w : Word LpmSymbol}
    (der :
      PreparedLinearDerives
        lpmPreparedLinearGrammar A w) :
    LpmLinearDerives A w := by
  induction der with
  | terminals p head tail hrhs =>
      cases p with
      | evC =>
          change
            PreparedLinearRhs.terminals c [] =
              PreparedLinearRhs.terminals head tail at hrhs
          cases hrhs
          exact LpmLinearDerives.ev_c
      | evWrap =>
          change
            PreparedLinearRhs.around [a] LpmLinearNT.odd [b] _ =
              PreparedLinearRhs.terminals head tail at hrhs
          cases hrhs
      | oddD =>
          change
            PreparedLinearRhs.terminals d [] =
              PreparedLinearRhs.terminals head tail at hrhs
          cases hrhs
          exact LpmLinearDerives.odd_d
      | oddWrap =>
          change
            PreparedLinearRhs.around [a] LpmLinearNT.ev [b] _ =
              PreparedLinearRhs.terminals head tail at hrhs
          cases hrhs
      | eeE =>
          change
            PreparedLinearRhs.terminals e [] =
              PreparedLinearRhs.terminals head tail at hrhs
          cases hrhs
          exact LpmLinearDerives.ee_e
      | eeWrap =>
          change
            PreparedLinearRhs.around [a] LpmLinearNT.ee [b] _ =
              PreparedLinearRhs.terminals head tail at hrhs
          cases hrhs
  | @around p left core right hnonunit hrhs word child ih =>
      cases p with
      | evC =>
          change
            PreparedLinearRhs.terminals c [] =
              PreparedLinearRhs.around
                left core right hnonunit at hrhs
          cases hrhs
      | evWrap =>
          change
            PreparedLinearRhs.around [a] LpmLinearNT.odd [b] _ =
              PreparedLinearRhs.around
                left core right hnonunit at hrhs
          cases hrhs
          simpa [lpmPreparedLinearGrammar] using
            LpmLinearDerives.ev_wrap_odd ih
      | oddD =>
          change
            PreparedLinearRhs.terminals d [] =
              PreparedLinearRhs.around
                left core right hnonunit at hrhs
          cases hrhs
      | oddWrap =>
          change
            PreparedLinearRhs.around [a] LpmLinearNT.ev [b] _ =
              PreparedLinearRhs.around
                left core right hnonunit at hrhs
          cases hrhs
          simpa [lpmPreparedLinearGrammar] using
            LpmLinearDerives.odd_wrap_ev ih
      | eeE =>
          change
            PreparedLinearRhs.terminals e [] =
              PreparedLinearRhs.around
                left core right hnonunit at hrhs
          cases hrhs
      | eeWrap =>
          change
            PreparedLinearRhs.around [a] LpmLinearNT.ee [b] _ =
              PreparedLinearRhs.around
                left core right hnonunit at hrhs
          cases hrhs
          simpa [lpmPreparedLinearGrammar] using
            LpmLinearDerives.ee_wrap ih

/-- Every displayed derivation is realized by the generic prepared grammar. -/
theorem lpmDisplayedDerives_to_prepared
    {A : LpmLinearNT}
    {w : Word LpmSymbol}
    (der : LpmLinearDerives A w) :
    PreparedLinearDerives
      lpmPreparedLinearGrammar A w := by
  induction der with
  | ev_c =>
      exact
        PreparedLinearDerives.terminals
          LpmLinearProd.evC c [] rfl
  | @ev_wrap_odd w der ih =>
      have h :=
        PreparedLinearDerives.around
          LpmLinearProd.evWrap [a]
          LpmLinearNT.odd [b]
          (by simp) rfl ih
      simpa [lpmPreparedLinearGrammar] using h
  | odd_d =>
      exact
        PreparedLinearDerives.terminals
          LpmLinearProd.oddD d [] rfl
  | @odd_wrap_ev w der ih =>
      have h :=
        PreparedLinearDerives.around
          LpmLinearProd.oddWrap [a]
          LpmLinearNT.ev [b]
          (by simp) rfl ih
      simpa [lpmPreparedLinearGrammar] using h
  | ee_e =>
      exact
        PreparedLinearDerives.terminals
          LpmLinearProd.eeE e [] rfl
  | @ee_wrap w der ih =>
      have h :=
        PreparedLinearDerives.around
          LpmLinearProd.eeWrap [a]
          LpmLinearNT.ee [b]
          (by simp) rfl ih
      simpa [lpmPreparedLinearGrammar] using h

theorem lpmPreparedDerives_iff_displayed
    (A : LpmLinearNT)
    (w : Word LpmSymbol) :
    PreparedLinearDerives
        lpmPreparedLinearGrammar A w
      ↔
    LpmLinearDerives A w :=
  ⟨lpmPreparedDerives_to_displayed,
    lpmDisplayedDerives_to_prepared⟩

/-- Initial-set language of the prepared linear grammar. -/
def LpmPreparedStartLanguage :
    Set (Word LpmSymbol) :=
  { w |
      PreparedLinearDerives
          lpmPreparedLinearGrammar .ev w ∨
      PreparedLinearDerives
          lpmPreparedLinearGrammar .ee w }

/--
The concrete PreparedLinearIndexedCFG generates exactly L_{±,e}.  This is
the formal linearity witness for the displayed grammar.
-/
theorem lpm_prepared_linear_language_eq :
    LpmPreparedStartLanguage =
      LpmLanguage := by
  calc
    LpmPreparedStartLanguage =
        LpmDisplayedLinearLanguage := by
      apply Set.ext
      intro w
      simp only [LpmPreparedStartLanguage,
        LpmDisplayedLinearLanguage]
      constructor
      · rintro (hev | hee)
        · exact Or.inl
            (lpmPreparedDerives_to_displayed hev)
        · exact Or.inr
            (lpmPreparedDerives_to_displayed hee)
      · rintro (hev | hee)
        · exact Or.inl
            (lpmDisplayedDerives_to_prepared hev)
        · exact Or.inr
            (lpmDisplayedDerives_to_prepared hee)
    _ = LpmLanguage :=
      lpm_displayed_linear_language_eq

end TCS1
end LeanCfgProject
