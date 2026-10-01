import LeanCfgProject.TCS1.V83LevelCodedTreeSyntax

/-!
# TCS #1 v83: level-coded tree contexts and legal node toggles

The Appendix substitutability proof repeatedly replaces one residual-height-i
node between its shortcut and clean forms.  This module represents a parsed
tree with one distinguished node as a typed zipper/context and proves the
serialization factorization needed for those local replacements.
-/

namespace LeanCfgProject
namespace TCS1

/--
A level-tree context of outer residual height n with one hole of residual
height i.
-/
inductive LevelTreeContext : Nat → Nat → Type
  | hole (i : Nat) : LevelTreeContext i i
  | left {j i : Nat} :
      LevelTreeContext j i →
      LevelTree j →
      LevelTreeContext (j + 1) i
  | right {j i : Nat} :
      LevelTree j →
      LevelTreeContext j i →
      LevelTreeContext (j + 1) i
  deriving Repr

/-- Fill the distinguished node of a level-tree context. -/
def LevelTreeContext.plug :
    {n i : Nat} →
      LevelTreeContext n i →
      LevelTree i →
      LevelTree n
  | _, _, .hole _, t => t
  | _, _, .left ctx sibling, t =>
      .node (ctx.plug t) sibling
  | _, _, .right sibling ctx, t =>
      .node sibling (ctx.plug t)

/-- Serialized prefix before the distinguished subtree. -/
def LevelTreeContext.prefix :
    {n i : Nat} →
      LevelTreeContext n i →
      Word LevelTreeSymbol
  | _, _, .hole _ => []
  | _, _, .left ctx sibling =>
      [LevelTreeSymbol.l] ++ ctx.prefix
  | _, _, .right sibling ctx =>
      [LevelTreeSymbol.l] ++ sibling.serialize ++ ctx.prefix

/-- Serialized suffix after the distinguished subtree. -/
def LevelTreeContext.suffix :
    {n i : Nat} →
      LevelTreeContext n i →
      Word LevelTreeSymbol
  | _, _, .hole _ => []
  | _, _, .left ctx sibling =>
      ctx.suffix ++ sibling.serialize ++ [LevelTreeSymbol.r]
  | _, _, .right sibling ctx =>
      ctx.suffix ++ [LevelTreeSymbol.r]

/--
Serialization factors through the zipper as prefix, focused subtree, suffix.
-/
theorem levelTreeContext_serialize_plug
    {n i : Nat}
    (ctx : LevelTreeContext n i)
    (t : LevelTree i) :
    (ctx.plug t).serialize =
      ctx.prefix ++ t.serialize ++ ctx.suffix := by
  induction ctx with
  | hole i =>
      simp [LevelTreeContext.plug,
        LevelTreeContext.prefix, LevelTreeContext.suffix]
  | @left j i ctx sibling ih =>
      simp [LevelTreeContext.plug, LevelTree.serialize,
        LevelTreeContext.prefix, LevelTreeContext.suffix,
        ih, List.append_assoc]
  | @right j i sibling ctx ih =>
      simp [LevelTreeContext.plug, LevelTree.serialize,
        LevelTreeContext.prefix, LevelTreeContext.suffix,
        ih, List.append_assoc]

/-- A shortcut plugged at any parsed node remains in the outer tree language. -/
theorem levelTreeContext_shortcut_mem
    {n i : Nat}
    (ctx : LevelTreeContext n i) :
    (ctx.plug (.shortcut i)).serialize ∈
      LevelTreeLanguage n := by
  exact ⟨ctx.plug (.shortcut i), rfl⟩

/-- A clean subtree plugged at the same node also remains in the language. -/
theorem levelTreeContext_clean_mem
    {n i : Nat}
    (ctx : LevelTreeContext n i) :
    (ctx.plug (cleanLevelTree i)).serialize ∈
      LevelTreeLanguage n := by
  exact ⟨ctx.plug (cleanLevelTree i), rfl⟩

/--
The shortcut-to-clean node toggle preserves exactly the external serialized
context.
-/
theorem levelTreeContext_shortcut_clean_same_context
    {n i : Nat}
    (ctx : LevelTreeContext n i) :
    ∃ u v : Word LevelTreeSymbol,
      (ctx.plug (.shortcut i)).serialize =
        u ++ (.shortcut i : LevelTree i).serialize ++ v
      ∧
      (ctx.plug (cleanLevelTree i)).serialize =
        u ++ (cleanLevelTree i).serialize ++ v := by
  refine ⟨ctx.prefix, ctx.suffix, ?_, ?_⟩
  · exact levelTreeContext_serialize_plug ctx (.shortcut i)
  · exact levelTreeContext_serialize_plug ctx (cleanLevelTree i)

end TCS1
end LeanCfgProject
