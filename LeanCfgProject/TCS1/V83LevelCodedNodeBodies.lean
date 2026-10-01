import LeanCfgProject.TCS1.V83LevelCodedTreeToggles

/-!
# TCS #1 v83: node bodies for the Appendix replacement argument

The manuscript's Appendix toggles the *body* of a parsed residual-height-i
node,

  s_i <-> b_i,

while keeping that node's surrounding l/r brackets fixed.  The tree zipper
developed earlier focused whole subtrees; this module refines the
serialization factorization to the exact body-level replacement used in the
paper.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Clean body b_0 = a and b_(i+1) = z_i z_i. -/
def levelCleanNodeBody : Nat → Word LevelTreeSymbol
  | 0 => [a]
  | i + 1 => cleanLevelTreeWord i ++ cleanLevelTreeWord i

@[simp] theorem cleanLevelTreeWord_head
    (i : Nat) :
    (cleanLevelTreeWord i).head? =
      some LevelTreeSymbol.l := by
  cases i <;> rfl

/-- Shortcut and clean node bodies always begin with different symbols. -/
theorem levelShortcutBody_head_ne_cleanNodeBody_head
    (i : Nat) :
    (levelShortcutBody i).head? ≠
      (levelCleanNodeBody i).head? := by
  cases i with
  | zero =>
      simp [levelShortcutBody, levelCleanNodeBody]
  | succ i =>
      simp [levelShortcutBody, levelCleanNodeBody,
        cleanLevelTreeWord_head]

/-- In particular, the literal shortcut and clean bodies are distinct. -/
theorem levelShortcutBody_ne_cleanNodeBody
    (i : Nat) :
    levelShortcutBody i ≠
      levelCleanNodeBody i := by
  intro h
  have hh :=
    congrArg List.head? h
  exact
    (levelShortcutBody_head_ne_cleanNodeBody_head i) hh

/-- The clean residual-height-i tree is l b_i r. -/
theorem cleanLevelTree_serialize_eq_bracket_body
    (i : Nat) :
    (cleanLevelTree i).serialize =
      [l] ++ levelCleanNodeBody i ++ [r] := by
  cases i with
  | zero =>
      simp [cleanLevelTree, LevelTree.serialize,
        levelCleanNodeBody]
  | succ i =>
      simp [cleanLevelTree, LevelTree.serialize,
        levelCleanNodeBody, cleanLevelTreeWord,
        List.append_assoc]

/-- The shortcut residual-height-i tree is l s_i r. -/
theorem shortcutLevelTree_serialize_eq_bracket_body
    (i : Nat) :
    (LevelTree.shortcut i).serialize =
      [l] ++ levelShortcutBody i ++ [r] := by
  simp [LevelTree.serialize]

/--
When a parsed context focuses a shortcut node, its serialization factors with
the exact literal body s_i exposed.
-/
theorem levelTreeContext_shortcut_body_factor
    {n i : Nat}
    (ctx : LevelTreeContext n i) :
    (ctx.plug (.shortcut i)).serialize =
      (ctx.prefix ++ [l]) ++
        levelShortcutBody i ++
        ([r] ++ ctx.suffix) := by
  rw [levelTreeContext_serialize_plug]
  rw [shortcutLevelTree_serialize_eq_bracket_body]
  simp [List.append_assoc]

/--
The matching clean expansion exposes b_i in precisely the same external word
context.
-/
theorem levelTreeContext_clean_body_factor
    {n i : Nat}
    (ctx : LevelTreeContext n i) :
    (ctx.plug (cleanLevelTree i)).serialize =
      (ctx.prefix ++ [l]) ++
        levelCleanNodeBody i ++
        ([r] ++ ctx.suffix) := by
  rw [levelTreeContext_serialize_plug]
  rw [cleanLevelTree_serialize_eq_bracket_body]
  simp [List.append_assoc]

/-- One literal manuscript replacement s_i <-> b_i inside a word. -/
inductive LevelBodyToggleStep :
    Word LevelTreeSymbol →
      Word LevelTreeSymbol → Prop
  | expand
      (i : Nat)
      (p q : Word LevelTreeSymbol) :
      LevelBodyToggleStep
        (p ++ levelShortcutBody i ++ q)
        (p ++ levelCleanNodeBody i ++ q)
  | contract
      (i : Nat)
      (p q : Word LevelTreeSymbol) :
      LevelBodyToggleStep
        (p ++ levelCleanNodeBody i ++ q)
        (p ++ levelShortcutBody i ++ q)

/-- Literal body toggling is symmetric. -/
theorem levelBodyToggleStep_symm
    {x y : Word LevelTreeSymbol}
    (h : LevelBodyToggleStep x y) :
    LevelBodyToggleStep y x := by
  cases h with
  | expand i p q =>
      exact LevelBodyToggleStep.contract i p q
  | contract i p q =>
      exact LevelBodyToggleStep.expand i p q

/--
Every legal parsed-tree toggle is exactly one literal body replacement in the
serialized word.
-/
theorem levelTreeToggle_to_bodyToggleStep
    {n : Nat}
    {s t : LevelTree n}
    (h : LevelTreeToggle s t) :
    LevelBodyToggleStep s.serialize t.serialize := by
  cases h with
  | @expand i ctx =>
      rw [levelTreeContext_shortcut_body_factor,
        levelTreeContext_clean_body_factor]
      exact
        LevelBodyToggleStep.expand
          i (ctx.prefix ++ [l]) ([r] ++ ctx.suffix)
  | @contract i ctx =>
      rw [levelTreeContext_clean_body_factor,
        levelTreeContext_shortcut_body_factor]
      exact
        LevelBodyToggleStep.contract
          i (ctx.prefix ++ [l]) ([r] ++ ctx.suffix)

/-- Literal body replacement preserves the external word context. -/
theorem levelBodyToggleStep_contextual
    {x y : Word LevelTreeSymbol}
    (h : LevelBodyToggleStep x y)
    (u v : Word LevelTreeSymbol) :
    LevelBodyToggleStep
      (u ++ x ++ v)
      (u ++ y ++ v) := by
  cases h with
  | expand i p q =>
      simpa [List.append_assoc] using
        (LevelBodyToggleStep.expand
          i (u ++ p) (q ++ v))
  | contract i p q =>
      simpa [List.append_assoc] using
        (LevelBodyToggleStep.contract
          i (u ++ p) (q ++ v))


/-- Finite reflexive-transitive closure of literal body replacements. -/
inductive LevelBodyToggleReach :
    Word LevelTreeSymbol →
      Word LevelTreeSymbol → Prop
  | refl (w : Word LevelTreeSymbol) :
      LevelBodyToggleReach w w
  | step {x y z : Word LevelTreeSymbol} :
      LevelBodyToggleStep x y →
      LevelBodyToggleReach y z →
      LevelBodyToggleReach x z

/-- Concatenate finite literal body-toggle sequences. -/
theorem levelBodyToggleReach_trans
    {x y z : Word LevelTreeSymbol}
    (hxy : LevelBodyToggleReach x y)
    (hyz : LevelBodyToggleReach y z) :
    LevelBodyToggleReach x z := by
  induction hxy with
  | refl =>
      exact hyz
  | @step a b y hab hby ih =>
      exact LevelBodyToggleReach.step hab (ih hyz)

/-- Reverse a finite literal body-toggle sequence. -/
theorem levelBodyToggleReach_symm
    {x y : Word LevelTreeSymbol}
    (hxy : LevelBodyToggleReach x y) :
    LevelBodyToggleReach y x := by
  induction hxy with
  | refl w =>
      exact LevelBodyToggleReach.refl w
  | @step a b y hab hby ih =>
      exact
        levelBodyToggleReach_trans
          ih
          (LevelBodyToggleReach.step
            (levelBodyToggleStep_symm hab)
            (LevelBodyToggleReach.refl a))

/-- Finite body-toggle reachability is stable under fixed external context. -/
theorem levelBodyToggleReach_contextual
    {x y : Word LevelTreeSymbol}
    (hxy : LevelBodyToggleReach x y)
    (u v : Word LevelTreeSymbol) :
    LevelBodyToggleReach
      (u ++ x ++ v)
      (u ++ y ++ v) := by
  induction hxy with
  | refl w =>
      exact LevelBodyToggleReach.refl _
  | @step a b y hab hby ih =>
      exact
        LevelBodyToggleReach.step
          (levelBodyToggleStep_contextual hab u v)
          ih

/--
A finite parsed-tree toggle sequence becomes a finite literal manuscript
body-replacement sequence after serialization.
-/
theorem levelTreeToggleReach_to_bodyToggleReach
    {n : Nat}
    {s t : LevelTree n}
    (hst : LevelTreeToggleReach s t) :
    LevelBodyToggleReach s.serialize t.serialize := by
  induction hst with
  | refl t =>
      exact LevelBodyToggleReach.refl _
  | @step s t u hst htu ih =>
      exact
        LevelBodyToggleReach.step
          (levelTreeToggle_to_bodyToggleStep hst)
          ih

/-- Any two words of T_n are connected by finite literal s_i <-> b_i moves. -/
theorem levelTreeLanguage_bodyToggle_connected
    {n : Nat}
    {x y : Word LevelTreeSymbol}
    (hx : x ∈ LevelTreeLanguage n)
    (hy : y ∈ LevelTreeLanguage n) :
    LevelBodyToggleReach x y := by
  rcases hx with ⟨sx, rfl⟩
  rcases hy with ⟨sy, rfl⟩
  exact
    levelTreeToggleReach_to_bodyToggleReach
      (levelTreeToggleReach_connected sx sy)

end TCS1
end LeanCfgProject
