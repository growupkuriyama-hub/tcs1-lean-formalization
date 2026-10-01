import LeanCfgProject.TCS1.V83LevelCodedIndexedGrammarBridge
import LeanCfgProject.TCS1.V83MixedDerivationInversion

/-!
# TCS #1 v83: exact indexed semantics of the compact grammar R_n^-

For n=m+1 the manuscript grammar R_n^- retains the ordinary A_i symbols
below the top level and adds A_i^- states.  This module proves the converse
of the existing direct-to-indexed bridge and therefore identifies the actual
finite indexed start language with T_n^-.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Indexed Z_k derivations in R_(m+1)^- are exactly the direct zero blocks. -/
theorem levelCodeRMinusIndexed_z_to_direct
    (m k : Nat)
    (hk : k ≤ m + 1)
    {w : Word LevelTreeSymbol}
    (hd :
      MixedDerives
        (levelCodeRMinusIndexedGrammar m).toMixedRules
        (.z ⟨k, by omega⟩) w) :
    LevelCodeZDerives k w := by
  induction k generalizing w with
  | zero =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with ⟨prod, hLhs, hRhs⟩
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
          | amShortcut j =>
              cases hLhs
          | amNodeLeft j =>
              cases hLhs
          | amNodeRight j =>
              cases hLhs
  | succ k ih =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with ⟨prod, hLhs, hRhs⟩
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
                    (⟨k, by omega⟩ : Fin (m + 2)) := by
                apply Fin.ext
                simpa [levelCodeFinEmbed] using hj
              have hz' :
                  MixedDerives
                    (levelCodeRMinusIndexedGrammar m).toMixedRules
                    (.z (⟨k, by omega⟩ :
                      Fin (m + 2))) z := by
                simpa [hfin] using hz
              have dz :
                  LevelCodeZDerives k z :=
                ih (show k ≤ m + 1 by omega) hz'
              simpa using
                (LevelCodeZDerives.succ dz)
          | a0Clean =>
              cases hLhs
          | aShortcut j =>
              cases hLhs
          | aNode j =>
              cases hLhs
          | amShortcut j =>
              cases hLhs
          | amNodeLeft j =>
              cases hLhs
          | amNodeRight j =>
              cases hLhs

/-- Indexed retained A_k derivations in R_(m+1)^- are direct A_k derivations. -/
theorem levelCodeRMinusIndexed_a_to_direct
    (m k : Nat)
    (hk : k ≤ m)
    {w : Word LevelTreeSymbol}
    (hd :
      MixedDerives
        (levelCodeRMinusIndexedGrammar m).toMixedRules
        (.a ⟨k, by omega⟩) w) :
    LevelCodeADerives k w := by
  induction k generalizing w with
  | zero =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with ⟨prod, hLhs, hRhs⟩
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
                mixedSymbolsDerive_three_terminals_inv hpieces
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
                levelCodeRMinusIndexed_z_to_direct
                  m j.1
                  (show j.1 ≤ m + 1 by omega) hz
              have da :=
                LevelCodeADerives.shortcut dz
              simpa [hval, List.append_assoc] using da
          | aNode j =>
              have hval : j.1 + 1 = 0 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              omega
          | amShortcut j =>
              cases hLhs
          | amNodeLeft j =>
              cases hLhs
          | amNodeRight j =>
              cases hLhs
  | succ k ih =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with ⟨prod, hLhs, hRhs⟩
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
                levelCodeRMinusIndexed_z_to_direct
                  m j.1
                  (show j.1 ≤ m + 1 by omega) hz
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
                    (⟨k, by omega⟩ : Fin (m + 1)) := by
                apply Fin.ext
                simpa [levelCodeFinEmbed] using hj
              have hx' :
                  MixedDerives
                    (levelCodeRMinusIndexedGrammar m).toMixedRules
                    (.a (⟨k, by omega⟩ :
                      Fin (m + 1))) x := by
                simpa [hfin] using hx
              have hy' :
                  MixedDerives
                    (levelCodeRMinusIndexedGrammar m).toMixedRules
                    (.a (⟨k, by omega⟩ :
                      Fin (m + 1))) y := by
                simpa [hfin] using hy
              have dx :
                  LevelCodeADerives k x :=
                ih (show k ≤ m by omega) hx'
              have dy :
                  LevelCodeADerives k y :=
                ih (show k ≤ m by omega) hy'
              simpa [List.append_assoc] using
                (LevelCodeADerives.node dx dy)
          | amShortcut j =>
              cases hLhs
          | amNodeLeft j =>
              cases hLhs
          | amNodeRight j =>
              cases hLhs

/-- Indexed A_k^- derivations are exactly the direct shortcut-containing ones. -/
theorem levelCodeRMinusIndexed_am_to_direct
    (m k : Nat)
    (hk : k ≤ m + 1)
    {w : Word LevelTreeSymbol}
    (hd :
      MixedDerives
        (levelCodeRMinusIndexedGrammar m).toMixedRules
        (.am ⟨k, by omega⟩) w) :
    LevelCodeAMinusDerives k w := by
  induction k generalizing w with
  | zero =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with ⟨prod, hLhs, hRhs⟩
          cases prod with
          | start =>
              cases hLhs
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
          | amShortcut j =>
              have hval : j.1 = 0 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              rw [← hRhs] at hpieces
              obtain ⟨z, hp, hz⟩ :=
                mixedSymbolsDerive_shortcut_inv hpieces
              subst pieces
              have dz :
                  LevelCodeZDerives j.1 z :=
                levelCodeRMinusIndexed_z_to_direct
                  m j.1
                  (show j.1 ≤ m + 1 by omega) hz
              have dm :=
                LevelCodeAMinusDerives.shortcut dz
              simpa [hval, List.append_assoc] using dm
          | amNodeLeft j =>
              have hval : j.1 + 1 = 0 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              omega
          | amNodeRight j =>
              have hval : j.1 + 1 = 0 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              omega
  | succ k ih =>
      cases hd with
      | @rule A rhs pieces hRule hpieces =>
          rcases hRule with ⟨prod, hLhs, hRhs⟩
          cases prod with
          | start =>
              cases hLhs
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
          | amShortcut j =>
              have hval : j.1 = k + 1 := by
                injection hLhs with hidx
                exact congrArg Fin.val hidx
              rw [← hRhs] at hpieces
              obtain ⟨z, hp, hz⟩ :=
                mixedSymbolsDerive_shortcut_inv hpieces
              subst pieces
              have dz :
                  LevelCodeZDerives j.1 z :=
                levelCodeRMinusIndexed_z_to_direct
                  m j.1
                  (show j.1 ≤ m + 1 by omega) hz
              have dm :=
                LevelCodeAMinusDerives.shortcut dz
              simpa [hval, List.append_assoc] using dm
          | amNodeLeft j =>
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
                    (⟨k, by omega⟩ : Fin (m + 2)) := by
                apply Fin.ext
                simpa [levelCodeFinEmbed] using hj
              have hx' :
                  MixedDerives
                    (levelCodeRMinusIndexedGrammar m).toMixedRules
                    (.am (⟨k, by omega⟩ :
                      Fin (m + 2))) x := by
                simpa [hfin] using hx
              have dx :
                  LevelCodeAMinusDerives k x :=
                ih (show k ≤ m + 1 by omega) hx'
              have dy :
                  LevelCodeADerives j.1 y :=
                levelCodeRMinusIndexed_a_to_direct
                  m j.1
                  (show j.1 ≤ m by omega) hy
              have dy' :
                  LevelCodeADerives k y := by
                simpa [hj] using dy
              have dm :=
                LevelCodeAMinusDerives.nodeLeft dx dy'
              simpa [List.append_assoc] using dm
          | amNodeRight j =>
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
                    (⟨k, by omega⟩ : Fin (m + 2)) := by
                apply Fin.ext
                simpa [levelCodeFinEmbed] using hj
              have hy' :
                  MixedDerives
                    (levelCodeRMinusIndexedGrammar m).toMixedRules
                    (.am (⟨k, by omega⟩ :
                      Fin (m + 2))) y := by
                simpa [hfin] using hy
              have dx :
                  LevelCodeADerives j.1 x :=
                levelCodeRMinusIndexed_a_to_direct
                  m j.1
                  (show j.1 ≤ m by omega) hx
              have dx' :
                  LevelCodeADerives k x := by
                simpa [hj] using dx
              have dy :
                  LevelCodeAMinusDerives k y :=
                ih (show k ≤ m + 1 by omega) hy'
              have dm :=
                LevelCodeAMinusDerives.nodeRight dx' dy
              simpa [List.append_assoc] using dm

/-- Any indexed start derivation of R_(m+1)^- belongs to T_(m+1)^-. -/
theorem levelCodeRMinusIndexed_start_to_language
    (m : Nat)
    {w : Word LevelTreeSymbol}
    (hd :
      MixedDerives
        (levelCodeRMinusIndexedGrammar m).toMixedRules
        LevelCodeRMinusNT.start w) :
    w ∈ LevelTreeShortcutLanguage (m + 1) := by
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
              LevelCodeAMinusDerives (m + 1) x :=
            levelCodeRMinusIndexed_am_to_direct
              m (m + 1) (le_rfl) hx
          simpa using
            (levelCodeAMinusDerives_to_shortcutLanguage dx)
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
      | amShortcut j =>
          cases hLhs
      | amNodeLeft j =>
          cases hLhs
      | amNodeRight j =>
          cases hLhs

/--
The actual finite indexed grammar R_(m+1)^- generates exactly the manuscript
target T_(m+1)^-.
-/
theorem levelCodeRMinusIndexed_start_language_eq
    (m : Nat) :
    MixedNonterminalLanguage
        (levelCodeRMinusIndexedGrammar m).toMixedRules
        LevelCodeRMinusNT.start =
      LevelTreeShortcutLanguage (m + 1) := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    exact levelCodeRMinusIndexed_start_to_language m hw
  · intro hw
    exact
      levelTreeShortcutLanguage_to_minusIndexed_start
        m hw

end TCS1
end LeanCfgProject
