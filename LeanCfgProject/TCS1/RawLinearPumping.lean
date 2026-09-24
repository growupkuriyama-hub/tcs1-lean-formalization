import LeanCfgProject.TCS1.LinearPumpingBounded
import LeanCfgProject.TCS1.LinearRawUnitFreePreparedBridge
import LeanCfgProject.TCS1.LinearConstructedStartLanguage
import LeanCfgProject.TCS1.LinearRegularIntersection

/-!
# TCS #1 v79: pumping theorem for finite raw linear grammars

The manuscript's Delta-star non-linearity reduction uses the ordinary class
of finite linear CFGs.  The repository represents that class by
RawLinearInitialRepresentable.

This module transports the bounded pumping lemma for the verified normalized
linear-spine grammar all the way back to an arbitrary finite raw linear
grammar.  No external pumping theorem is assumed.

For a raw grammar G the pumping threshold is the number of states in the
concrete linear-spine normalization of its finite epsilon/unit-free prepared
grammar.  Every sufficiently long raw derivation is translated to that
normalization, pumped there, and translated back.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section RawLinearPumping

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]

/-- Concrete pumping threshold attached to one finite raw linear grammar. -/
noncomputable def rawLinearPumpingThreshold
    (G : RawLinearIndexedCFG N α P) : Nat :=
  Fintype.card
    (LinearConstructedState
      (rawLinearPreparedGrammar G))

/--
Every sufficiently long raw derivation has the bounded two-sided pumping
decomposition required by the linear pumping lemma.
-/
theorem rawLinearDerives_pumping_bounded
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : Word α}
    (d : RawLinearDerives G A word)
    (hlong :
      rawLinearPumpingThreshold G < word.length) :
    ∃ u v x y z : Word α,
      word = u ++ v ++ x ++ y ++ z
      ∧
      0 < (v ++ y).length
      ∧
      (u ++ v ++ y ++ z).length
        ≤ rawLinearPumpingThreshold G
      ∧
      ∀ n : Nat,
        RawLinearDerives G A
          (u ++
            linearPumpLeft v n ++
            x ++
            linearPumpRight y n ++
            z) := by
  classical
  let Gp := rawLinearPreparedGrammar G
  have hne : word ≠ [] := by
    intro hw
    subst word
    simp [rawLinearPumpingThreshold] at hlong
  have de :
      RawLinearEpsilonFreeDerives G A word :=
    rawLinearDerives_to_epsilonFree G d hne
  have du :
      RawLinearUnitFreeDerives G A word :=
    rawLinearEpsilonFreeDerives_to_unitFree G de
  have dp :
      PreparedLinearDerives Gp A word := by
    simpa [Gp] using
      (rawLinearUnitFreeDerives_to_prepared G du)
  have dc :
      UntypedDerives
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (linearOldState Gp A)
        word :=
    preparedLinearDerives_to_linearConstructed Gp dp
  have hshape :
      LinearSpineShape
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (LinearConstructedWrapper Gp) := by
    let hu :=
      linearConstructed_untypedLinearSpineShape Gp
    exact
      { wrapper_terminal := hu.wrapper_terminal
        wrapper_no_binary := hu.wrapper_no_binary
        binary_children := hu.binary_children }
  have hthreshold :
      rawLinearPumpingThreshold G =
        Fintype.card (LinearConstructedState Gp) := by
    rfl
  have hlong' :
      Fintype.card (LinearConstructedState Gp) <
        word.length := by
    rw [← hthreshold]
    exact hlong
  have hp :=
    linearSpine_pumping_bounded
      (LinearConstructedTerminalRule Gp)
      (LinearConstructedBinaryRule Gp)
      (LinearConstructedWrapper Gp)
      hshape
      (linearConstructedWrapper_old Gp A)
      dc
      hlong'
  rcases hp with
    ⟨u, v, x, y, z,
      heq, hpos, hbound, hpump⟩
  refine
    ⟨u, v, x, y, z,
      heq, hpos, ?_, ?_⟩
  · rw [hthreshold]
    exact hbound
  · intro n
    have dc' :=
      hpump n
    have dp' :
        PreparedLinearDerives Gp A
          (u ++
            linearPumpLeft v n ++
            x ++
            linearPumpRight y n ++
            z) :=
      linearConstructed_old_derives_to_prepared
        Gp dc'
    have du' :
        RawLinearUnitFreeDerives G A
          (u ++
            linearPumpLeft v n ++
            x ++
            linearPumpRight y n ++
            z) := by
      simpa [Gp] using
        (preparedDerives_to_rawLinearUnitFree G dp')
    exact
      rawLinearEpsilonFreeDerives_to_raw G
        (rawLinearUnitFreeDerives_to_epsilonFree
          G du')

/--
Uniform pumping property for a finite initial set of a fixed raw grammar.
The threshold is independent of the chosen initial nonterminal.
-/
theorem rawLinearInitialLanguage_pumping_bounded
    (G : RawLinearIndexedCFG N α P)
    (I : Set N) :
    ∀ word : Word α,
      word ∈ RawLinearInitialLanguage G I →
      rawLinearPumpingThreshold G < word.length →
      ∃ u v x y z : Word α,
        word = u ++ v ++ x ++ y ++ z
        ∧
        0 < (v ++ y).length
        ∧
        (u ++ v ++ y ++ z).length
          ≤ rawLinearPumpingThreshold G
        ∧
        ∀ n : Nat,
          u ++
              linearPumpLeft v n ++
              x ++
              linearPumpRight y n ++
              z
            ∈ RawLinearInitialLanguage G I := by
  intro word hword hlong
  rcases hword with ⟨A, hAI, dA⟩
  obtain
    ⟨u, v, x, y, z,
      heq, hpos, hbound, hpump⟩ :=
    rawLinearDerives_pumping_bounded
      G dA hlong
  refine
    ⟨u, v, x, y, z,
      heq, hpos, hbound, ?_⟩
  intro n
  exact
    ⟨A, hAI, hpump n⟩

end RawLinearPumping

/--
Language-level pumping property shared by every finite raw-linear
initial-set presentation.
-/
def RawLinearPumpingProperty
    {α : Type v}
    (L : Set (Word α)) : Prop :=
  ∃ p : Nat,
    ∀ word : Word α,
      word ∈ L →
      p < word.length →
      ∃ u v x y z : Word α,
        word = u ++ v ++ x ++ y ++ z
        ∧
        0 < (v ++ y).length
        ∧
        (u ++ v ++ y ++ z).length ≤ p
        ∧
        ∀ n : Nat,
          u ++
              linearPumpLeft v n ++
              x ++
              linearPumpRight y n ++
              z
            ∈ L

/--
Every finite raw-linear initial-set presentation satisfies the bounded linear
pumping property.
-/
theorem rawLinearInitialRepresentable_pumping
    {α : Type v}
    [Fintype α]
    {L : Set (Word α)}
    (hL :
      RawLinearInitialRepresentable.{u, v, w} L) :
    RawLinearPumpingProperty L := by
  classical
  rcases hL with
    ⟨N, fN, P, fP, G, I, hIfin, hlang⟩
  letI : Fintype N := fN
  letI : Fintype P := fP
  refine
    ⟨rawLinearPumpingThreshold G, ?_⟩
  intro word hword hlong
  have hraw :
      word ∈ RawLinearInitialLanguage G I := by
    rw [hlang]
    exact hword
  obtain
    ⟨u, v, x, y, z,
      heq, hpos, hbound, hpump⟩ :=
    rawLinearInitialLanguage_pumping_bounded
      G I word hraw hlong
  refine
    ⟨u, v, x, y, z,
      heq, hpos, hbound, ?_⟩
  intro n
  rw [← hlang]
  exact hpump n

end TCS1
end LeanCfgProject
