import LeanCfgProject.TCS1.DeltaStarBinaryGrammar
import LeanCfgProject.TCS1.DeltaStarNonregular
import LeanCfgProject.TCS1.DeltaStarNonlinearityBridge
import LeanCfgProject.TCS1.DeltaStarNonlinearityReduction

/-!
# TCS #1 v78: paper-facing Delta-star proposition package

This module packages the machine-checked components of the manuscript's
nonlinear Delta-star example.

Verified here, by reference to the preceding modules:

* the displayed CFG `S -> T S | epsilon`, `T -> a T b | epsilon`
  generates exactly the parser language;
* an explicit finite binary CFG has exactly the same initial language;
* the language is nonregular;
* it is substitutable for the finite monoid homomorphism `h_star`;
* it lies outside every fixed prefix--suffix window class;
* the manuscript's non-linearity reduction identity
  `Delta* ∩ a* b* a* b* = Delta Delta` holds extensionally.

The non-linearity clause is now internal as well.  The repository proves a
bounded pumping lemma for arbitrary finite raw-linear presentations, applies
it to Double Delta, and combines that obstruction with the verified regular
four-block intersection reduction.  Thus no external non-linearity theorem is
assumed by the paper-facing package.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

/--
Paper-facing verified core of the nonlinear fixed-h-star example.

This theorem keeps the original semantic clauses grouped together; the
unconditional non-linearity conclusion is supplied by the full package below.
-/
theorem nonlinear_rs_example_verified_core :
    (∀ w : Word Symbol,
      SDerives w ↔ w ∈ Language)
    ∧
    (initial.Finite ∧
      InitialSetLanguage
        binaryGrammar initial =
      Language)
    ∧
    (¬ FormalLanguage.IsRegular)
    ∧
    (Language ∩ FourBlockLanguage =
      DoubleDeltaLanguage)
    ∧
    FixedHSubstitutable
      starTyping Language
    ∧
    (∀ k l : Nat,
      ¬ FixedWindowSubstitutable
        k l Language) := by
  refine ⟨displayedDerives_iff_language, ?_⟩
  refine ⟨finite_cfg_witness, ?_⟩
  refine ⟨not_regular, ?_⟩
  refine ⟨language_inter_fourBlock_eq_doubleDelta, ?_⟩
  exact
    deltaStar_fixedH_and_outside_all_fixedWindows


universe u w

/--
Reusable conditional form of the Proposition 9.1 non-linearity reduction.
The hypothesis is discharged internally by
doubleDelta_not_rawLinearInitialRepresentable in the full package below.
-/
theorem nonlinear_rs_example_nonlinearity_reduction
    (hDouble :
      ¬ RawLinearInitialRepresentable.{u, 0, w}
        DoubleDeltaLanguage) :
    ¬ RawLinearInitialRepresentable.{u, 0, w}
        Language :=
  deltaStar_not_rawLinearRepresentable_of_doubleDelta
    hDouble



/--
Full paper-facing Proposition 9.1 package, including unconditional
non-linearity in the finite raw-linear presentation semantics.
-/
theorem nonlinear_rs_example_full
    : (∀ w : Word Symbol,
        SDerives w ↔ w ∈ Language)
      ∧
      (initial.Finite ∧
        InitialSetLanguage
          binaryGrammar initial =
        Language)
      ∧
      (¬ FormalLanguage.IsRegular)
      ∧
      (¬ RawLinearInitialRepresentable.{u, 0, w}
          Language)
      ∧
      FixedHSubstitutable
        starTyping Language
      ∧
      (∀ k l : Nat,
        ¬ FixedWindowSubstitutable
          k l Language) := by
  refine ⟨displayedDerives_iff_language, ?_⟩
  refine ⟨finite_cfg_witness, ?_⟩
  refine ⟨not_regular, ?_⟩
  refine ⟨deltaStar_not_rawLinearRepresentable, ?_⟩
  exact
    deltaStar_fixedH_and_outside_all_fixedWindows

end DeltaStar
end TCS1
end LeanCfgProject
