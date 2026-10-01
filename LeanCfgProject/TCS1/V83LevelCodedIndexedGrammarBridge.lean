import LeanCfgProject.TCS1.V83LevelCodedIndexedGrammar
import LeanCfgProject.TCS1.GeneralCFGDerivation

/-!
# TCS #1 v83: direct-to-indexed derivation bridge for R_n

This module starts the semantic bridge from the paper-facing derivation
relations to the actual finite indexed CFG presentation of R_n.  It proves
that every direct Z_i or A_i derivation is realized by the generic
MixedDerives semantics, and hence every word of T_n is generated from the
indexed start symbol.

The converse direction is kept separate so that the two inclusions can be
audited independently.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Direct Z_i derivations are realized by the indexed grammar R_n. -/
theorem levelCodeZDerives_to_indexed
    {i n : Nat}
    {w : Word LevelTreeSymbol}
    (d : LevelCodeZDerives i w)
    (hi : i ≤ n) :
    MixedDerives
      (levelCodeRIndexedGrammar n).toMixedRules
      (.z ⟨i, by omega⟩) w := by
  induction d generalizing n with
  | zero =>
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.z (levelCodeFinZero n))
            [Sum.inr zero] :=
        ⟨LevelCodeRProd.z0, rfl, rfl⟩
      have hd :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.z (levelCodeFinZero n))
            [zero] :=
        mixedDerives_terminal
          (levelCodeRIndexedGrammar n).toMixedRules hr
      simpa [levelCodeFinZero] using hd
  | @succ i w d ih =>
      have hi' : i < n := by omega
      let fi : Fin n := ⟨i, hi'⟩
      have hchild :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.z (levelCodeFinEmbed fi)) w := by
        simpa [fi, levelCodeFinEmbed] using
          (ih (n := n) (show i ≤ n by omega))
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.z (levelCodeFinSucc fi))
            [Sum.inl (.z (levelCodeFinEmbed fi)),
              Sum.inr zero] :=
        ⟨LevelCodeRProd.zSucc fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRIndexedGrammar n).toMixedRules
            [Sum.inl (.z (levelCodeFinEmbed fi)),
              Sum.inr zero]
            [w, [zero]] :=
        MixedSymbolsDerive.nonterminal hchild
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.nil))
      have hd :=
        MixedDerives.rule hr hs
      simpa [fi, levelCodeFinSucc] using hd

/-- Direct A_i derivations are realized by the indexed grammar R_n. -/
theorem levelCodeADerives_to_indexed
    {i n : Nat}
    {w : Word LevelTreeSymbol}
    (d : LevelCodeADerives i w)
    (hi : i ≤ n) :
    MixedDerives
      (levelCodeRIndexedGrammar n).toMixedRules
      (.a ⟨i, by omega⟩) w := by
  induction d generalizing n with
  | clean0 =>
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.a (levelCodeFinZero n))
            [Sum.inr l, Sum.inr a, Sum.inr r] :=
        ⟨LevelCodeRProd.a0Clean, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRIndexedGrammar n).toMixedRules
            [Sum.inr l, Sum.inr a, Sum.inr r]
            [[l], [a], [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.terminal
              (MixedSymbolsDerive.nil)))
      have hd :=
        MixedDerives.rule hr hs
      simpa [levelCodeFinZero] using hd
  | @shortcut i z dz =>
      let fi : Fin (n + 1) := ⟨i, by omega⟩
      have hz :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.z fi) z := by
        simpa [fi] using
          (levelCodeZDerives_to_indexed dz hi)
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.a fi)
            [Sum.inr l, Sum.inr c,
              Sum.inl (.z fi),
              Sum.inr d, Sum.inr r] :=
        ⟨LevelCodeRProd.aShortcut fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRIndexedGrammar n).toMixedRules
            [Sum.inr l, Sum.inr c,
              Sum.inl (.z fi),
              Sum.inr d, Sum.inr r]
            [[l], [c], z, [d], [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.nonterminal hz
              (MixedSymbolsDerive.terminal
                (MixedSymbolsDerive.terminal
                  (MixedSymbolsDerive.nil)))))
      have hd :=
        MixedDerives.rule hr hs
      simpa [fi, List.append_assoc] using hd
  | @node i x y dx dy ihX ihY =>
      have hi' : i < n := by omega
      let fi : Fin n := ⟨i, hi'⟩
      have hx :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.a (levelCodeFinEmbed fi)) x := by
        simpa [fi, levelCodeFinEmbed] using
          (ihX (n := n) (show i ≤ n by omega))
      have hy :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.a (levelCodeFinEmbed fi)) y := by
        simpa [fi, levelCodeFinEmbed] using
          (ihY (n := n) (show i ≤ n by omega))
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.a (levelCodeFinSucc fi))
            [Sum.inr l,
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inr r] :=
        ⟨LevelCodeRProd.aNode fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRIndexedGrammar n).toMixedRules
            [Sum.inr l,
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inr r]
            [[l], x, y, [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.nonterminal hx
            (MixedSymbolsDerive.nonterminal hy
              (MixedSymbolsDerive.terminal
                (MixedSymbolsDerive.nil))))
      have hd :=
        MixedDerives.rule hr hs
      simpa [fi, levelCodeFinSucc, List.append_assoc] using hd

/-- Every T_n word is generated from the actual indexed start symbol of R_n. -/
theorem levelTreeLanguage_to_indexed_start
    (n : Nat)
    {w : Word LevelTreeSymbol}
    (hw : w ∈ LevelTreeLanguage n) :
    MixedDerives
      (levelCodeRIndexedGrammar n).toMixedRules
      (LevelCodeRNT.start) w := by
  rcases hw with ⟨t, rfl⟩
  have hA :
      MixedDerives
        (levelCodeRIndexedGrammar n).toMixedRules
        (.a (levelCodeFinTop n))
        t.serialize := by
    simpa [levelCodeFinTop] using
      (levelCodeADerives_to_indexed
        (levelTree_to_levelCodeADerives t)
        (le_rfl : n ≤ n))
  have hr :
      (levelCodeRIndexedGrammar n).toMixedRules
        (LevelCodeRNT.start)
        [Sum.inl (.a (levelCodeFinTop n))] :=
    ⟨LevelCodeRProd.start, rfl, rfl⟩
  exact mixedDerives_unit
    (levelCodeRIndexedGrammar n).toMixedRules
    hr hA


/-- Direct Z_i derivations are realized by the indexed grammar R_(m+1)^-. -/
theorem levelCodeZDerives_to_minusIndexed
    {i m : Nat}
    {w : Word LevelTreeSymbol}
    (d : LevelCodeZDerives i w)
    (hi : i ≤ m + 1) :
    MixedDerives
      (levelCodeRMinusIndexedGrammar m).toMixedRules
      (.z ⟨i, by omega⟩) w := by
  induction d generalizing m with
  | zero =>
      have hr :
          (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.z (levelCodeFinZero (m + 1)))
            [Sum.inr zero] :=
        ⟨LevelCodeRMinusProd.z0, rfl, rfl⟩
      have hd :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.z (levelCodeFinZero (m + 1)))
            [zero] :=
        mixedDerives_terminal
          (levelCodeRMinusIndexedGrammar m).toMixedRules hr
      simpa [levelCodeFinZero] using hd
  | @succ i w d ih =>
      have hi' : i < m + 1 := by omega
      let fi : Fin (m + 1) := ⟨i, hi'⟩
      have hchild :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.z (levelCodeFinEmbed fi)) w := by
        simpa [fi, levelCodeFinEmbed] using
          (ih (m := m) (show i ≤ m + 1 by omega))
      have hr :
          (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.z (levelCodeFinSucc fi))
            [Sum.inl (.z (levelCodeFinEmbed fi)),
              Sum.inr zero] :=
        ⟨LevelCodeRMinusProd.zSucc fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            [Sum.inl (.z (levelCodeFinEmbed fi)),
              Sum.inr zero]
            [w, [zero]] :=
        MixedSymbolsDerive.nonterminal hchild
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.nil))
      have hd := MixedDerives.rule hr hs
      simpa [fi, levelCodeFinSucc] using hd

/-- Retained direct A_i derivations are realized by R_(m+1)^- for i <= m. -/
theorem levelCodeADerives_to_minusIndexed
    {i m : Nat}
    {w : Word LevelTreeSymbol}
    (d : LevelCodeADerives i w)
    (hi : i ≤ m) :
    MixedDerives
      (levelCodeRMinusIndexedGrammar m).toMixedRules
      (.a ⟨i, by omega⟩) w := by
  induction d generalizing m with
  | clean0 =>
      have hr :
          (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.a (levelCodeFinZero m))
            [Sum.inr l, Sum.inr a, Sum.inr r] :=
        ⟨LevelCodeRMinusProd.a0Clean, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            [Sum.inr l, Sum.inr a, Sum.inr r]
            [[l], [a], [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.terminal
              (MixedSymbolsDerive.nil)))
      have hd := MixedDerives.rule hr hs
      simpa [levelCodeFinZero] using hd
  | @shortcut i z dz =>
      let fi : Fin (m + 1) := ⟨i, by omega⟩
      have hz :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.z (levelCodeFinEmbed fi)) z := by
        simpa [fi, levelCodeFinEmbed] using
          (levelCodeZDerives_to_minusIndexed
            dz (m := m) (show i ≤ m + 1 by omega))
      have hr :
          (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.a fi)
            [Sum.inr l, Sum.inr c,
              Sum.inl (.z (levelCodeFinEmbed fi)),
              Sum.inr d, Sum.inr r] :=
        ⟨LevelCodeRMinusProd.aShortcut fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            [Sum.inr l, Sum.inr c,
              Sum.inl (.z (levelCodeFinEmbed fi)),
              Sum.inr d, Sum.inr r]
            [[l], [c], z, [d], [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.nonterminal hz
              (MixedSymbolsDerive.terminal
                (MixedSymbolsDerive.terminal
                  (MixedSymbolsDerive.nil)))))
      have hd := MixedDerives.rule hr hs
      simpa [fi, List.append_assoc] using hd
  | @node i x y dx dy ihX ihY =>
      have hi' : i < m := by omega
      let fi : Fin m := ⟨i, hi'⟩
      have hx :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.a (levelCodeFinEmbed fi)) x := by
        simpa [fi, levelCodeFinEmbed] using
          (ihX (m := m) (show i ≤ m by omega))
      have hy :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.a (levelCodeFinEmbed fi)) y := by
        simpa [fi, levelCodeFinEmbed] using
          (ihY (m := m) (show i ≤ m by omega))
      have hr :
          (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.a (levelCodeFinSucc fi))
            [Sum.inr l,
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inr r] :=
        ⟨LevelCodeRMinusProd.aNode fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            [Sum.inr l,
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inr r]
            [[l], x, y, [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.nonterminal hx
            (MixedSymbolsDerive.nonterminal hy
              (MixedSymbolsDerive.terminal
                (MixedSymbolsDerive.nil))))
      have hd := MixedDerives.rule hr hs
      simpa [fi, levelCodeFinSucc,
        List.append_assoc] using hd

/-- Direct A_i^- derivations are realized by the indexed grammar R_(m+1)^-. -/
theorem levelCodeAMinusDerives_to_minusIndexed
    {i m : Nat}
    {w : Word LevelTreeSymbol}
    (der : LevelCodeAMinusDerives i w)
    (hi : i ≤ m + 1) :
    MixedDerives
      (levelCodeRMinusIndexedGrammar m).toMixedRules
      (.am ⟨i, by omega⟩) w := by
  induction der generalizing m with
  | @shortcut i z dz =>
      let fi : Fin (m + 2) := ⟨i, by omega⟩
      have hz :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.z fi) z := by
        simpa [fi] using
          (levelCodeZDerives_to_minusIndexed
            dz (m := m) hi)
      have hr :
          (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.am fi)
            [Sum.inr l, Sum.inr c,
              Sum.inl (.z fi),
              Sum.inr d, Sum.inr r] :=
        ⟨LevelCodeRMinusProd.amShortcut fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            [Sum.inr l, Sum.inr c,
              Sum.inl (.z fi),
              Sum.inr d, Sum.inr r]
            [[l], [c], z, [d], [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.nonterminal hz
              (MixedSymbolsDerive.terminal
                (MixedSymbolsDerive.terminal
                  (MixedSymbolsDerive.nil)))))
      have hd := MixedDerives.rule hr hs
      simpa [fi, List.append_assoc] using hd
  | @nodeLeft i x y dx dy ih =>
      have hi' : i < m + 1 := by omega
      let fi : Fin (m + 1) := ⟨i, hi'⟩
      have hx :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.am (levelCodeFinEmbed fi)) x := by
        simpa [fi, levelCodeFinEmbed] using
          (ih (m := m) (show i ≤ m + 1 by omega))
      have hy :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.a fi) y := by
        simpa [fi] using
          (levelCodeADerives_to_minusIndexed
            dy (m := m) (show i ≤ m by omega))
      have hr :
          (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.am (levelCodeFinSucc fi))
            [Sum.inr l,
              Sum.inl (.am (levelCodeFinEmbed fi)),
              Sum.inl (.a fi),
              Sum.inr r] :=
        ⟨LevelCodeRMinusProd.amNodeLeft fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            [Sum.inr l,
              Sum.inl (.am (levelCodeFinEmbed fi)),
              Sum.inl (.a fi),
              Sum.inr r]
            [[l], x, y, [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.nonterminal hx
            (MixedSymbolsDerive.nonterminal hy
              (MixedSymbolsDerive.terminal
                (MixedSymbolsDerive.nil))))
      have hd := MixedDerives.rule hr hs
      simpa [fi, levelCodeFinSucc,
        List.append_assoc] using hd
  | @nodeRight i x y dx dy ih =>
      have hi' : i < m + 1 := by omega
      let fi : Fin (m + 1) := ⟨i, hi'⟩
      have hx :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.a fi) x := by
        simpa [fi] using
          (levelCodeADerives_to_minusIndexed
            dx (m := m) (show i ≤ m by omega))
      have hy :
          MixedDerives
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.am (levelCodeFinEmbed fi)) y := by
        simpa [fi, levelCodeFinEmbed] using
          (ih (m := m) (show i ≤ m + 1 by omega))
      have hr :
          (levelCodeRMinusIndexedGrammar m).toMixedRules
            (.am (levelCodeFinSucc fi))
            [Sum.inr l,
              Sum.inl (.a fi),
              Sum.inl (.am (levelCodeFinEmbed fi)),
              Sum.inr r] :=
        ⟨LevelCodeRMinusProd.amNodeRight fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRMinusIndexedGrammar m).toMixedRules
            [Sum.inr l,
              Sum.inl (.a fi),
              Sum.inl (.am (levelCodeFinEmbed fi)),
              Sum.inr r]
            [[l], x, y, [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.nonterminal hx
            (MixedSymbolsDerive.nonterminal hy
              (MixedSymbolsDerive.terminal
                (MixedSymbolsDerive.nil))))
      have hd := MixedDerives.rule hr hs
      simpa [fi, levelCodeFinSucc,
        List.append_assoc] using hd

/--
Every T_(m+1)^- word is generated from the actual indexed start symbol of
R_(m+1)^-.
-/
theorem levelTreeShortcutLanguage_to_minusIndexed_start
    (m : Nat)
    {w : Word LevelTreeSymbol}
    (hw : w ∈ LevelTreeShortcutLanguage (m + 1)) :
    MixedDerives
      (levelCodeRMinusIndexedGrammar m).toMixedRules
      (LevelCodeRMinusNT.start) w := by
  have hdirect :
      LevelCodeAMinusDerives (m + 1) w :=
    (levelCodeAMinusDerives_iff_shortcutLanguage
      (m + 1) w).2 hw
  have hA :
      MixedDerives
        (levelCodeRMinusIndexedGrammar m).toMixedRules
        (.am (levelCodeFinTop (m + 1))) w := by
    simpa [levelCodeFinTop] using
      (levelCodeAMinusDerives_to_minusIndexed
        hdirect (m := m)
        (le_rfl : m + 1 ≤ m + 1))
  have hr :
      (levelCodeRMinusIndexedGrammar m).toMixedRules
        (LevelCodeRMinusNT.start)
        [Sum.inl
          (.am (levelCodeFinTop (m + 1)))] :=
    ⟨LevelCodeRMinusProd.start, rfl, rfl⟩
  exact mixedDerives_unit
    (levelCodeRMinusIndexedGrammar m).toMixedRules
    hr hA

end TCS1
end LeanCfgProject
