import LeanCfgProject.TCS1.V83LevelCodedTreeTyping
import LeanCfgProject.TCS1.V83LevelCodedTreeContexts

/-!
# TCS #1 v83: unique parsing of level-coded tree serializations

The Appendix proof of level-coded substitutability uses unique parsing.
This module gives an executable prefix parser indexed by residual height and
proves that parsing a serialization recovers exactly the original tree and
the untouched suffix.  In particular, serialization is injective.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Consume exactly k zero symbols from the front of a word. -/
def consumeLevelZeros : Nat → Word LevelTreeSymbol →
    Option (Word LevelTreeSymbol)
  | 0, xs => some xs
  | k + 1, zero :: xs => consumeLevelZeros k xs
  | _ + 1, _ => none

@[simp] theorem consumeLevelZeros_replicate_append
    (k : Nat)
    (suffix : Word LevelTreeSymbol) :
    consumeLevelZeros k
        (List.replicate k zero ++ suffix) =
      some suffix := by
  induction k with
  | zero =>
      simp [consumeLevelZeros]
  | succ k ih =>
      exact ih

/-- Every serialized level tree begins with the left bracket. -/
theorem levelTree_serialize_starts_l
    {n : Nat}
    (t : LevelTree n) :
    ∃ rest : Word LevelTreeSymbol,
      t.serialize = l :: rest := by
  cases t <;>
    simp [LevelTree.serialize, levelShortcutBody]

/--
Parse one residual-height-n tree from the front of a word and return the
unconsumed suffix.
-/
def parseLevelTreePrefix :
    (n : Nat) → Word LevelTreeSymbol →
      Option (LevelTree n × Word LevelTreeSymbol)
  | 0, l :: a :: r :: suffix =>
      some (.cleanLeaf, suffix)
  | 0, l :: c :: xs =>
      match consumeLevelZeros 1 xs with
      | some (d :: r :: suffix) =>
          some (.shortcut 0, suffix)
      | _ => none
  | 0, _ => none
  | n + 1, l :: c :: xs =>
      match consumeLevelZeros (n + 2) xs with
      | some (d :: r :: suffix) =>
          some (.shortcut (n + 1), suffix)
      | _ => none
  | n + 1, l :: xs =>
      match parseLevelTreePrefix n xs with
      | some (left, ys) =>
          match parseLevelTreePrefix n ys with
          | some (right, r :: suffix) =>
              some (.node left right, suffix)
          | _ => none
      | none => none
  | _ + 1, _ => none

/--
The prefix parser is a left inverse to serialization, uniformly in an
arbitrary following suffix.
-/
@[simp] theorem parseLevelTreePrefix_serialize_append
    {n : Nat}
    (t : LevelTree n)
    (suffix : Word LevelTreeSymbol) :
    parseLevelTreePrefix n (t.serialize ++ suffix) =
      some (t, suffix) := by
  induction t generalizing suffix with
  | cleanLeaf =>
      simp [LevelTree.serialize, parseLevelTreePrefix]
  | shortcut n =>
      cases n with
      | zero =>
          simp [LevelTree.serialize, levelShortcutBody,
            parseLevelTreePrefix,
            consumeLevelZeros_replicate_append,
            List.append_assoc]
      | succ n =>
          simp [LevelTree.serialize, levelShortcutBody,
            parseLevelTreePrefix,
            consumeLevelZeros_replicate_append,
            List.append_assoc, Nat.succ_eq_add_one,
            Nat.add_assoc]
  | @node n left right ihL ihR =>
      obtain ⟨leftRest, hstart⟩ :=
        levelTree_serialize_starts_l left
      have hL :=
        ihL (right.serialize ++ [r] ++ suffix)
      have hR :=
        ihR ([r] ++ suffix)
      rw [hstart] at hL
      simp [LevelTree.serialize, hstart,
        parseLevelTreePrefix, List.append_assoc,
        hL, hR]

@[simp] theorem parseLevelTreePrefix_serialize
    {n : Nat}
    (t : LevelTree n) :
    parseLevelTreePrefix n t.serialize =
      some (t, []) := by
  simpa using
    (parseLevelTreePrefix_serialize_append t [])

/-- Every serialized level-n tree has a unique level-n parse. -/
theorem levelTree_serialize_injective
    {n : Nat} :
    Function.Injective
      (fun t : LevelTree n => t.serialize) := by
  intro t u h
  have hp :=
    congrArg (parseLevelTreePrefix n) h
  simp at hp
  exact hp

/--
Extensional unique-parse form used by the manuscript: two residual-height-n
trees with the same serialized word are equal.
-/
theorem levelTree_unique_parse
    {n : Nat}
    {t u : LevelTree n}
    (h : t.serialize = u.serialize) :
    t = u :=
  levelTree_serialize_injective h

end TCS1
end LeanCfgProject
