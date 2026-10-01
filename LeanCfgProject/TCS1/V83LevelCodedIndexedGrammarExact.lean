import LeanCfgProject.TCS1.V83LevelCodedIndexedGrammarBridge
import LeanCfgProject.TCS1.V83MixedDerivationInversion

/-!
# TCS #1 v83: exact indexed semantics of the compact grammar R_n

The forward bridge from the paper-facing direct semantics to the actual finite
indexed grammar is already available in the indexed-grammar bridge module.
This module proves the converse direction for R_n by induction on the
residual-height index.  Consequently the finite indexed presentation generates
exactly the manuscript language T_n.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/--
Any indexed derivation from Z_k in R_n is one of the direct zero-block
derivations.
-/
theorem levelCodeRIndexed_z_to_direct
    (n k : Nat)
    (hk : k ≤ n)
    {w : Word LevelTreeSymbol}
    (hd :
      MixedDerives
        (levelCodeRIndexedGrammar n).toMixedRules
        (.z ⟨k, by omega⟩) w) :
    LevelCodeZDerives k w := by
  induction k generalizing w with
  | zero =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with
            ⟨prod, hLhs, hRhs⟩
          cases prod with
          | start =>
              cases hLhs
          | z0 =>
              rw [← hRhs] at hpieces
              have hp :
                  pieces = [[zero]] :=
                mixedSymbolsDerive_terminal_inv hpieces
              subst pieces
              simpa using LevelCodeZDerives.zero
          | zSucc j =>
              have hval : j.1 + 1 = 0 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              omega
          | a0Clean =>
              cases hLhs
          | aShortcut j =>
              cases hLhs
          | aNode j =>
              cases hLhs
  | succ k ih =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with
            ⟨prod, hLhs, hRhs⟩
          cases prod with
          | start =>
              cases hLhs
          | z0 =>
              have hval : 0 = k + 1 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              omega
          | zSucc j =>
              have hval : j.1 + 1 = k + 1 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              have hj : j.1 = k := by omega
              rw [← hRhs] at hpieces
              obtain ⟨z, hp, hz⟩ :=
                mixedSymbolsDerive_nonterminal_terminal_inv
                  hpieces
              subst pieces
              have hfin :
                  levelCodeFinEmbed j =
                    (⟨k, by omega⟩ : Fin (n + 1)) := by
                apply Fin.ext
                simpa [levelCodeFinEmbed] using hj
              have hz' :
                  MixedDerives
                    (levelCodeRIndexedGrammar n).toMixedRules
                    (.z (⟨k, by omega⟩ :
                      Fin (n + 1))) z := by
                simpa [hfin] using hz
              have dz :
                  LevelCodeZDerives k z :=
                ih (show k ≤ n by omega) hz'
              simpa using
                (LevelCodeZDerives.succ dz)
          | a0Clean =>
              cases hLhs
          | aShortcut j =>
              cases hLhs
          | aNode j =>
              cases hLhs

/--
Any indexed derivation from A_k in R_n is one of the direct level-coded-tree
derivations.
-/
theorem levelCodeRIndexed_a_to_direct
    (n k : Nat)
    (hk : k ≤ n)
    {w : Word LevelTreeSymbol}
    (hd :
      MixedDerives
        (levelCodeRIndexedGrammar n).toMixedRules
        (.a ⟨k, by omega⟩) w) :
    LevelCodeADerives k w := by
  induction k generalizing w with
  | zero =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with
            ⟨prod, hLhs, hRhs⟩
          cases prod with
          | start =>
              cases hLhs
          | z0 =>
              cases hLhs
          | zSucc j =>
              cases hLhs
          | a0Clean =>
              rw [← hRhs] at hpieces
              have hp :
                  pieces = [[l], [a], [r]] :=
                mixedSymbolsDerive_three_terminals_inv
                  hpieces
              subst pieces
              simpa using LevelCodeADerives.clean0
          | aShortcut j =>
              have hval : j.1 = 0 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              rw [← hRhs] at hpieces
              obtain ⟨z, hp, hz⟩ :=
                mixedSymbolsDerive_shortcut_inv hpieces
              subst pieces
              have dz :
                  LevelCodeZDerives j.1 z :=
                levelCodeRIndexed_z_to_direct
                  n j.1
                  (show j.1 ≤ n by omega) hz
              have da :=
                LevelCodeADerives.shortcut dz
              simpa [hval, List.append_assoc] using da
          | aNode j =>
              have hval : j.1 + 1 = 0 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              omega
  | succ k ih =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with
            ⟨prod, hLhs, hRhs⟩
          cases prod with
          | start =>
              cases hLhs
          | z0 =>
              cases hLhs
          | zSucc j =>
              cases hLhs
          | a0Clean =>
              have hval : 0 = k + 1 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              omega
          | aShortcut j =>
              have hval : j.1 = k + 1 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              rw [← hRhs] at hpieces
              obtain ⟨z, hp, hz⟩ :=
                mixedSymbolsDerive_shortcut_inv hpieces
              subst pieces
              have dz :
                  LevelCodeZDerives j.1 z :=
                levelCodeRIndexed_z_to_direct
                  n j.1
                  (show j.1 ≤ n by omega) hz
              have da :=
                LevelCodeADerives.shortcut dz
              simpa [hval, List.append_assoc] using da
          | aNode j =>
              have hval : j.1 + 1 = k + 1 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              have hj : j.1 = k := by omega
              rw [← hRhs] at hpieces
              obtain ⟨x, y, hp, hx, hy⟩ :=
                mixedSymbolsDerive_binary_bracket_inv
                  hpieces
              subst pieces
              have hfin :
                  levelCodeFinEmbed j =
                    (⟨k, by omega⟩ : Fin (n + 1)) := by
                apply Fin.ext
                simpa [levelCodeFinEmbed] using hj
              have hx' :
                  MixedDerives
                    (levelCodeRIndexedGrammar n).toMixedRules
                    (.a (⟨k, by omega⟩ :
                      Fin (n + 1))) x := by
                simpa [hfin] using hx
              have hy' :
                  MixedDerives
                    (levelCodeRIndexedGrammar n).toMixedRules
                    (.a (⟨k, by omega⟩ :
                      Fin (n + 1))) y := by
                simpa [hfin] using hy
              have dx :
                  LevelCodeADerives k x :=
                ih (show k ≤ n by omega) hx'
              have dy :
                  LevelCodeADerives k y :=
                ih (show k ≤ n by omega) hy'
              simpa [List.append_assoc] using
                (LevelCodeADerives.node dx dy)

/-- Any indexed start derivation of R_n belongs to T_n. -/
theorem levelCodeRIndexed_start_to_language
    (n : Nat)
    {w : Word LevelTreeSymbol}
    (hd :
      MixedDerives
        (levelCodeRIndexedGrammar n).toMixedRules
        LevelCodeRNT.start w) :
    w ∈ LevelTreeLanguage n := by
  cases hd with
  | @rule A rhs pieces hRule hpieces =>
      rcases hRule with ⟨prod, hLhs, hRhs⟩
      cases prod with
      | start =>
          rw [← hRhs] at hpieces
          obtain ⟨x, hp, hx⟩ :=
            mixedSymbolsDerive_unit_inv hpieces
          subst pieces
          have dx :
              LevelCodeADerives n x :=
            levelCodeRIndexed_a_to_direct
              n n (le_rfl) hx
          simpa using
            (levelCodeADerives_to_language dx)
      | z0 =>
          cases hLhs
      | zSucc j =>
          cases hLhs
      | a0Clean =>
          cases hLhs
      | aShortcut j =>
          cases hLhs
      | aNode j =>
          cases hLhs

/--
The actual finite indexed grammar R_n generates exactly the manuscript target
T_n.
-/
theorem levelCodeRIndexed_start_language_eq
    (n : Nat) :
    MixedNonterminalLanguage
        (levelCodeRIndexedGrammar n).toMixedRules
        LevelCodeRNT.start =
      LevelTreeLanguage n := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    exact levelCodeRIndexed_start_to_language n hw
  · intro hw
    exact levelTreeLanguage_to_indexed_start n hw

end TCS1
end LeanCfgProject
