import LeanCfgProject.TCS1.ReconstructionSoundness
import LeanCfgProject.TCS1.GeneralCFGDerivation

/-!
# TCS #1 v79: concrete CFG presentation of reconstruction rules R1--R4

The reconstruction semantics used in Sections 4--6 was originally represented
directly by the inductive relation `HypDerives`.  This module begins the
presentation bridge needed by the executable membership layer: it packages the
same four rule schemata as an ordinary mixed CFG.

A reconstruction nonterminal stores exactly the paper-facing triple
`[x;u,v]`.  Finiteness is handled in the next layer by restricting these
symbols to the occurrence-indexed support extracted from the finite sample.

This file proves the sound direction of the representation bridge: every
`HypDerives` tree is literally a `MixedDerives` tree of the concrete CFG.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ReconstructionCFGPresentation

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Paper-facing reconstruction nonterminal `[x;u,v]`. -/
@[ext] structure ReconstructionNonterminal
    (α : Type u) where
  factor : Word α
  leftContext : Word α
  rightContext : Word α
deriving DecidableEq

/--
Ordinary mixed-CFG presentation of rules R1--R4.

The constructors deliberately mirror `HypDerives` one-for-one.  The
observation premises keep the ambient nonterminal type harmlessly infinite;
only finitely many states can participate for a fixed finite sample.
-/
inductive ReconstructionMixedRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    MixedRules (ReconstructionNonterminal α) α
  | r4
      {a : α} {u v : Word α}
      (hobs : Observed K [a] u v) :
      ReconstructionMixedRule H K
        ⟨[a], u, v⟩
        [Sum.inr a]
  | r3
      {x x' u v : Word α}
      (hobs : Observed K x u v)
      (hobs' : Observed K x' u v)
      (htype : H.h x = H.h x') :
      ReconstructionMixedRule H K
        ⟨x, u, v⟩
        [Sum.inl ⟨x', u, v⟩]
  | r2
      {x u v u' v' : Word α}
      (hobs : Observed K x u v)
      (hobs' : Observed K x u' v') :
      ReconstructionMixedRule H K
        ⟨x, u, v⟩
        [Sum.inl ⟨x, u', v'⟩]
  | r1
      {x y u v : Word α}
      (hparent : Observed K (x ++ y) u v)
      (hleft : Observed K x u (y ++ v))
      (hright : Observed K y (u ++ x) v) :
      ReconstructionMixedRule H K
        ⟨x ++ y, u, v⟩
        [ Sum.inl ⟨x, u, y ++ v⟩,
          Sum.inl ⟨y, u ++ x, v⟩ ]

/--
Every derivation in the original reconstruction semantics is a derivation in
the ordinary mixed CFG with the matching paper-facing nonterminal.
-/
theorem hypDerives_to_reconstructionMixedDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    MixedDerives
      (ReconstructionMixedRule H K)
      ⟨x, u, v⟩
      w := by
  induction d with
  | @r4 a u v hobs =>
      exact
        mixedDerives_terminal
          (ReconstructionMixedRule H K)
          (ReconstructionMixedRule.r4 hobs)
  | @r3 x x' u v w hobs hobs' htype d ih =>
      exact
        mixedDerives_unit
          (ReconstructionMixedRule H K)
          (ReconstructionMixedRule.r3 hobs hobs' htype)
          ih
  | @r2 x u v u' v' w hobs hobs' d ih =>
      exact
        mixedDerives_unit
          (ReconstructionMixedRule H K)
          (ReconstructionMixedRule.r2 hobs hobs')
          ih
  | @r1 x y u v w₁ w₂ hparent hleft hright dleft dright ihleft ihrigh =>
      exact
        mixedDerives_binary
          (ReconstructionMixedRule H K)
          (ReconstructionMixedRule.r1 hparent hleft hright)
          ihleft ihrigh

/--
Set-valued form of the forward bridge for one observed reconstruction
nonterminal.
-/
theorem hypLanguage_subset_reconstructionMixedLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (x u v : Word α) :
    {w | HypDerives H K x u v w} ⊆
      MixedNonterminalLanguage
        (ReconstructionMixedRule H K)
        ⟨x, u, v⟩ := by
  intro w hw
  exact hypDerives_to_reconstructionMixedDerives H K hw

end ReconstructionCFGPresentation

end TCS1
end LeanCfgProject
