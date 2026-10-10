import LeanCfgProject.TCS1.V144HornClosure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.GCongr

/-!
# TCS #1 v144: the executable SSBNF normalizer (stages after binarization)

This file implements, with step counts, the part of the normalization of
`prop:thick-ssbnf-normal` that runs after terminal isolation and binarization
(appendix `app:thick-ssbnf`):

1. nullable states (Horn closure);
2. non-start ε-elimination **after** binarization: every binary rule
   `A → B C` is kept and contributes at most two unit rules
   `A → C` (if `B` nullable) and `A → B` (if `C` nullable) — at most three
   variants per binary rule, no `2^k` subset enumeration;
3. unit closure (one Horn closure per source state);
4. unit elimination: terminal and binary rules copied to every
   unit-predecessor;
5. productive states (Horn closure);
6. states reachable from the start through productive binary rules
   (Horn closure);
7. output: the reduced terminal/binary grammar on the reachable states, the
   separated start and the ε flag.

The input is an explicit *code* of a binary grammar with ε and unit rules
(`FrontCode`): lists of states and rules.  The state type is generic; atom
comparison is the costed parameter `ceq` (see `V144HornClosure`).  The front
end (terminal isolation and binarization of an indexed CFG) and the
connection with the existing semantic normalization are in
`V144SSBNFFrontEnd` / `V144SSBNFBridge`.

**Cost model.**  As in `V135CostedPrimitives` and `V144HornClosure`: value
and step count come from the same recursion; one step per list cell visited
or created, per loop iteration, and per atom comparison step reported by
`ceq`.  Building one constant-size rule record (a tuple and a body of at most
two cells, plus its output cell) is charged 4 steps.  No `Finset` operation,
hashing or sorting is executed.
-/

namespace LeanCfgProject
namespace TCS1
namespace SSBNFNorm

open Horn PolyBuild

universe u v w

section Combinators

variable {β : Type u} {γ : Type v}

/-- Map building constant-size records: 4 steps per element, 1 for `[]`. -/
def mapC (f : β → γ) : List β → List γ × Nat
  | [] => ([], 1)
  | b :: l => (f b :: (mapC f l).1, (mapC f l).2 + 4)

theorem mapC_fst (f : β → γ) : ∀ l : List β, (mapC f l).1 = l.map f
  | [] => rfl
  | b :: l => by simp [mapC, mapC_fst f l]

theorem mapC_snd (f : β → γ) : ∀ l : List β, (mapC f l).2 = 4 * l.length + 1
  | [] => rfl
  | b :: l => by simp [mapC, mapC_snd f l]; ring

/-- Append, copying the spine of the first list. -/
def appendC : List β → List β → List β × Nat
  | [], l₂ => (l₂, 1)
  | a :: l₁, l₂ => (a :: (appendC l₁ l₂).1, (appendC l₁ l₂).2 + 1)

theorem appendC_fst : ∀ l₁ l₂ : List β, (appendC l₁ l₂).1 = l₁ ++ l₂
  | [], _ => rfl
  | a :: l₁, l₂ => by simp [appendC, appendC_fst l₁ l₂]

theorem appendC_snd : ∀ l₁ l₂ : List β, (appendC l₁ l₂).2 = l₁.length + 1
  | [], _ => rfl
  | a :: l₁, l₂ => by simp [appendC, appendC_snd l₁ l₂]

/-- Filter with a costed test. -/
def filterC (p : β → Bool × Nat) : List β → List β × Nat
  | [] => ([], 1)
  | b :: l =>
      if (p b).1 then (b :: (filterC p l).1, (p b).2 + (filterC p l).2 + 1)
      else ((filterC p l).1, (p b).2 + (filterC p l).2 + 1)

theorem filterC_fst (p : β → Bool × Nat) :
    ∀ l : List β, (filterC p l).1 = l.filter (fun b => (p b).1)
  | [] => rfl
  | b :: l => by
      unfold filterC
      split_ifs with h
      · simp [List.filter_cons, h, filterC_fst p l]
      · simp [List.filter_cons, h, filterC_fst p l]

theorem mem_filterC (p : β → Bool × Nat) (l : List β) (b : β) :
    b ∈ (filterC p l).1 ↔ b ∈ l ∧ (p b).1 = true := by
  rw [filterC_fst, List.mem_filter]

theorem filterC_length_le (p : β → Bool × Nat) (l : List β) :
    (filterC p l).1.length ≤ l.length := by
  rw [filterC_fst]; exact List.length_filter_le _ _

theorem filterC_snd_le (p : β → Bool × Nat) (c : Nat) :
    ∀ l : List β, (∀ b, b ∈ l → (p b).2 ≤ c) →
      (filterC p l).2 ≤ l.length * (c + 1) + 1
  | [], _ => by simp [filterC]
  | b :: l, h => by
      have h1 := h b (by simp)
      have h2 := filterC_snd_le p c l (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
      have e : (l.length + 1) * (c + 1) = l.length * (c + 1) + c + 1 := by ring
      unfold filterC
      split_ifs
      · simp only [List.length_cons]; rw [e]; omega
      · simp only [List.length_cons]; rw [e]; omega

theorem sum_map_const_le (l : List β) (f : β → Nat) (c : Nat)
    (h : ∀ b, b ∈ l → f b ≤ c) : (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons b l ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have h1 := h b (by simp)
      have h2 := ih (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
      have e : (l.length + 1) * c = l.length * c + c := by ring
      omega

/-- `forListC` with a uniform per-iteration bound. -/
theorem forListC_bound_const (f : β → List γ × Nat) (c : Nat) (l : List β)
    (hf : ∀ b, b ∈ l → (f b).1.length ≤ (f b).2 ∧ (f b).2 ≤ c) :
    (forListC f l).1.length ≤ (forListC f l).2 ∧
      (forListC f l).2 ≤ l.length * (2 * c + 1) + 1 := by
  obtain ⟨h1, h2⟩ := forListC_bound f (fun _ => c) l hf
  refine ⟨h1, le_trans h2 ?_⟩
  have := sum_map_const_le l (fun _ => 2 * c + 1) (2 * c + 1) (fun _ _ => le_refl _)
  omega

theorem forListC_length_le (f : β → List γ × Nat) (k : Nat) :
    ∀ l : List β, (∀ b, b ∈ l → (f b).1.length ≤ k) →
      (forListC f l).1.length ≤ l.length * k
  | [], _ => by simp [forListC]
  | b :: l, h => by
      have h1 := h b (by simp)
      have h2 := forListC_length_le f k l (fun b' hb' => h b' (List.mem_cons_of_mem _ hb'))
      show ((f b).1 ++ (forListC f l).1).length ≤ _
      rw [List.length_append, List.length_cons]
      have e : (l.length + 1) * k = l.length * k + k := by ring
      omega

end Combinators

/-- Explicit code of a binary grammar with ε and unit rules. -/
structure FrontCode (S : Type u) (α : Type v) where
  states : List S
  term : List (S × α)
  bin : List (S × S × S)
  unit : List (S × S)
  eps : List S

/-- Explicit code of a reduced separated-start SSBNF grammar. -/
structure SSBNFCode (S : Type u) (α : Type v) where
  nonterminals : List S
  terminal : List (S × α)
  binary : List (S × S × S)
  start : Option S
  epsilon : Bool

section Stages

variable {S : Type u} {α : Type v} [DecidableEq S]
variable (ceq : S → S → Bool × Nat)

/-! ### Stage 1: nullable states -/

/-- Horn clauses for nullability. -/
def nullRules (g : FrontCode S α) : List (S × List S) :=
  g.eps.map (fun x => (x, [])) ++
    (g.unit.map (fun p => (p.1, [p.2])) ++
      g.bin.map (fun t => (t.1, [t.2.1, t.2.2])))

/-- Costed construction of the nullability clauses. -/
def nullRulesC (g : FrontCode S α) : List (S × List S) × Nat :=
  ((appendC (mapC (fun x => (x, ([] : List S))) g.eps).1
      (appendC (mapC (fun p : S × S => (p.1, [p.2])) g.unit).1
        (mapC (fun t : S × S × S => (t.1, [t.2.1, t.2.2])) g.bin).1).1).1,
    (mapC (fun x => (x, ([] : List S))) g.eps).2 +
      (mapC (fun p : S × S => (p.1, [p.2])) g.unit).2 +
      (mapC (fun t : S × S × S => (t.1, [t.2.1, t.2.2])) g.bin).2 +
      (appendC (mapC (fun p : S × S => (p.1, [p.2])) g.unit).1
        (mapC (fun t : S × S × S => (t.1, [t.2.1, t.2.2])) g.bin).1).2 +
      (appendC (mapC (fun x => (x, ([] : List S))) g.eps).1
        (appendC (mapC (fun p : S × S => (p.1, [p.2])) g.unit).1
          (mapC (fun t : S × S × S => (t.1, [t.2.1, t.2.2])) g.bin).1).1).2)

theorem nullRulesC_fst (g : FrontCode S α) : (nullRulesC g).1 = nullRules g := by
  simp [nullRulesC, nullRules, appendC_fst, mapC_fst]

/-- Nullable states. -/
def nullC (g : FrontCode S α) : List S × Nat :=
  ((hornC ceq g.states (nullRulesC g).1).1,
    (nullRulesC g).2 + (hornC ceq g.states (nullRulesC g).1).2 + 1)

/-! ### Stage 2: ε-elimination (at most three variants per binary rule) -/

/-- `A → C` for every `A → B C` with `B` nullable. -/
def dropLeftC (null : List S) : List (S × S × S) → List (S × S) × Nat
  | [] => ([], 1)
  | t :: ts =>
      if (memC ceq t.2.1 null).1 then
        ((t.1, t.2.2) :: (dropLeftC null ts).1,
          (memC ceq t.2.1 null).2 + (dropLeftC null ts).2 + 2)
      else
        ((dropLeftC null ts).1, (memC ceq t.2.1 null).2 + (dropLeftC null ts).2 + 1)

/-- `A → B` for every `A → B C` with `C` nullable. -/
def dropRightC (null : List S) : List (S × S × S) → List (S × S) × Nat
  | [] => ([], 1)
  | t :: ts =>
      if (memC ceq t.2.2 null).1 then
        ((t.1, t.2.1) :: (dropRightC null ts).1,
          (memC ceq t.2.2 null).2 + (dropRightC null ts).2 + 2)
      else
        ((dropRightC null ts).1, (memC ceq t.2.2 null).2 + (dropRightC null ts).2 + 1)

/-- Unit rules after ε-elimination: original, drop-left, drop-right. -/
def epsUnitC (g : FrontCode S α) (null : List S) : List (S × S) × Nat :=
  ((appendC g.unit (appendC (dropLeftC ceq null g.bin).1
      (dropRightC ceq null g.bin).1).1).1,
    (dropLeftC ceq null g.bin).2 + (dropRightC ceq null g.bin).2 +
      (appendC (dropLeftC ceq null g.bin).1 (dropRightC ceq null g.bin).1).2 +
      (appendC g.unit (appendC (dropLeftC ceq null g.bin).1
        (dropRightC ceq null g.bin).1).1).2)

/-! ### Stage 3: unit closure -/

/-- Horn clauses for the unit successors of a fixed source `x`. -/
def unitRulesFrom (eunit : List (S × S)) (x : S) : List (S × List S) :=
  (x, []) :: eunit.map (fun p => (p.2, [p.1]))

/-- Unit successors of one source, written as pairs `(x, z)`. -/
def reachFromC (states : List S) (eunit : List (S × S)) (x : S) :
    List (S × S) × Nat :=
  ((mapC (fun z => (x, z))
      (hornC ceq states ((x, []) :: (mapC (fun p : S × S => (p.2, [p.1])) eunit).1)).1).1,
    (mapC (fun p : S × S => (p.2, [p.1])) eunit).2 +
      (hornC ceq states ((x, []) :: (mapC (fun p : S × S => (p.2, [p.1])) eunit).1)).2 +
      (mapC (fun z => (x, z))
        (hornC ceq states ((x, []) :: (mapC (fun p : S × S => (p.2, [p.1])) eunit).1)).1).2
      + 1)

/-- The unit closure: all pairs `(x, z)` with `z` unit-reachable from `x`. -/
def unitClosureC (states : List S) (eunit : List (S × S)) : List (S × S) × Nat :=
  forListC (reachFromC ceq states eunit) states

/-! ### Stage 4: unit elimination (copy rules to unit predecessors) -/

/-- Terminal rules of `y` copied to `x`, for one closure pair `(x, y)`. -/
def copyTermC (term : List (S × α)) (p : S × S) : List (S × α) × Nat :=
  forListC (fun q : S × α =>
    if (ceq p.2 q.1).1 then ([(p.1, q.2)], (ceq p.2 q.1).2 + 1)
    else ([], (ceq p.2 q.1).2 + 1)) term

/-- Binary rules of `y` copied to `x`, for one closure pair `(x, y)`. -/
def copyBinC (bin : List (S × S × S)) (p : S × S) : List (S × S × S) × Nat :=
  forListC (fun q : S × S × S =>
    if (ceq p.2 q.1).1 then ([(p.1, q.2.1, q.2.2)], (ceq p.2 q.1).2 + 1)
    else ([], (ceq p.2 q.1).2 + 1)) bin

def unitFreeTermC (term : List (S × α)) (ureach : List (S × S)) : List (S × α) × Nat :=
  forListC (copyTermC ceq term) ureach

def unitFreeBinC (bin : List (S × S × S)) (ureach : List (S × S)) :
    List (S × S × S) × Nat :=
  forListC (copyBinC ceq bin) ureach

/-! ### Stage 5: productive states -/

def prodRules (uterm : List (S × α)) (ubin : List (S × S × S)) : List (S × List S) :=
  uterm.map (fun p => (p.1, [])) ++ ubin.map (fun t => (t.1, [t.2.1, t.2.2]))

def prodRulesC (uterm : List (S × α)) (ubin : List (S × S × S)) :
    List (S × List S) × Nat :=
  ((appendC (mapC (fun p : S × α => (p.1, ([] : List S))) uterm).1
      (mapC (fun t : S × S × S => (t.1, [t.2.1, t.2.2])) ubin).1).1,
    (mapC (fun p : S × α => (p.1, ([] : List S))) uterm).2 +
      (mapC (fun t : S × S × S => (t.1, [t.2.1, t.2.2])) ubin).2 +
      (appendC (mapC (fun p : S × α => (p.1, ([] : List S))) uterm).1
        (mapC (fun t : S × S × S => (t.1, [t.2.1, t.2.2])) ubin).1).2)

theorem prodRulesC_fst (uterm : List (S × α)) (ubin : List (S × S × S)) :
    (prodRulesC uterm ubin).1 = prodRules uterm ubin := by
  simp [prodRulesC, prodRules, appendC_fst, mapC_fst]

/-! ### Stage 6: reachability from the start -/

/-- Binary rules whose three states are all productive. -/
def prodBinC (prod : List S) (ubin : List (S × S × S)) : List (S × S × S) × Nat :=
  filterC (fun t : S × S × S =>
    ((memC ceq t.1 prod).1 && (memC ceq t.2.1 prod).1 && (memC ceq t.2.2 prod).1,
      (memC ceq t.1 prod).2 + (memC ceq t.2.1 prod).2 + (memC ceq t.2.2 prod).2 + 1))
    ubin

def reachRules (s : S) (pbin : List (S × S × S)) : List (S × List S) :=
  (s, []) :: pbin.flatMap (fun t => [(t.2.1, [t.1]), (t.2.2, [t.1])])

def reachRulesC (s : S) (pbin : List (S × S × S)) : List (S × List S) × Nat :=
  ((s, []) :: (forListC (fun t : S × S × S =>
      ([(t.2.1, [t.1]), (t.2.2, [t.1])], 5)) pbin).1,
    (forListC (fun t : S × S × S => ([(t.2.1, [t.1]), (t.2.2, [t.1])], 5)) pbin).2 + 1)

/-! ### Stage 7: output -/

def outTermC (reach : List S) (uterm : List (S × α)) : List (S × α) × Nat :=
  filterC (fun p : S × α => ((memC ceq p.1 reach).1, (memC ceq p.1 reach).2 + 1)) uterm

def outBinC (reach : List S) (pbin : List (S × S × S)) : List (S × S × S) × Nat :=
  filterC (fun t : S × S × S => ((memC ceq t.1 reach).1, (memC ceq t.1 reach).2 + 1)) pbin

/-! ### The whole normalizer -/

/-- All intermediate results of the normalizer, with the total step count. -/
structure Trace (S : Type u) (α : Type v) where
  null : List S
  eunit : List (S × S)
  ureach : List (S × S)
  uterm : List (S × α)
  ubin : List (S × S × S)
  prod : List S
  pbin : List (S × S × S)
  reach : List S
  out : SSBNFCode S α
  steps : Nat

/-- The executable normalizer on a front-end code with start state `s`. -/
def normalizeTrace (g : FrontCode S α) (s : S) : Trace S α :=
  let n := nullC ceq g
  let e := epsUnitC ceq g n.1
  let r := unitClosureC ceq g.states e.1
  let ut := unitFreeTermC ceq g.term r.1
  let ub := unitFreeBinC ceq g.bin r.1
  let pr := prodRulesC ut.1 ub.1
  let p := hornC ceq g.states pr.1
  let pb := prodBinC ceq p.1 ub.1
  let rr := reachRulesC s pb.1
  let rc := hornC ceq g.states rr.1
  let ot := outTermC ceq rc.1 ut.1
  let ob := outBinC ceq rc.1 pb.1
  let sp := memC ceq s p.1
  let ep := memC ceq s n.1
  { null := n.1, eunit := e.1, ureach := r.1, uterm := ut.1, ubin := ub.1,
    prod := p.1, pbin := pb.1, reach := rc.1,
    out :=
      if sp.1 then
        { nonterminals := rc.1, terminal := ot.1, binary := ob.1,
          start := some s, epsilon := ep.1 }
      else
        { nonterminals := [], terminal := [], binary := [],
          start := none, epsilon := ep.1 },
    steps := n.2 + e.2 + r.2 + ut.2 + ub.2 + pr.2 + p.2 + pb.2 + rr.2 + rc.2 +
      ot.2 + ob.2 + sp.2 + ep.2 + 1 }

end Stages


section TraceFields

variable {S : Type u} {α : Type v} [DecidableEq S]
variable (ceq : S → S → Bool × Nat) (g : FrontCode S α) (s : S)

theorem trace_null : (normalizeTrace ceq g s).null = (nullC ceq g).1 := rfl
theorem trace_eunit : (normalizeTrace ceq g s).eunit =
    (epsUnitC ceq g (normalizeTrace ceq g s).null).1 := rfl
theorem trace_ureach : (normalizeTrace ceq g s).ureach =
    (unitClosureC ceq g.states (normalizeTrace ceq g s).eunit).1 := rfl
theorem trace_uterm : (normalizeTrace ceq g s).uterm =
    (unitFreeTermC ceq g.term (normalizeTrace ceq g s).ureach).1 := rfl
theorem trace_ubin : (normalizeTrace ceq g s).ubin =
    (unitFreeBinC ceq g.bin (normalizeTrace ceq g s).ureach).1 := rfl
theorem trace_prod : (normalizeTrace ceq g s).prod =
    (hornC ceq g.states (prodRulesC (normalizeTrace ceq g s).uterm
      (normalizeTrace ceq g s).ubin).1).1 := rfl
theorem trace_pbin : (normalizeTrace ceq g s).pbin =
    (prodBinC ceq (normalizeTrace ceq g s).prod (normalizeTrace ceq g s).ubin).1 := rfl
theorem trace_reach : (normalizeTrace ceq g s).reach =
    (hornC ceq g.states (reachRulesC s (normalizeTrace ceq g s).pbin).1).1 := rfl

theorem trace_out :
    (normalizeTrace ceq g s).out =
      if (memC ceq s (normalizeTrace ceq g s).prod).1 then
        { nonterminals := (normalizeTrace ceq g s).reach,
          terminal := (outTermC ceq (normalizeTrace ceq g s).reach
            (normalizeTrace ceq g s).uterm).1,
          binary := (outBinC ceq (normalizeTrace ceq g s).reach
            (normalizeTrace ceq g s).pbin).1,
          start := some s,
          epsilon := (memC ceq s (normalizeTrace ceq g s).null).1 }
      else
        { nonterminals := [], terminal := [], binary := [], start := none,
          epsilon := (memC ceq s (normalizeTrace ceq g s).null).1 } := rfl

theorem trace_steps :
    (normalizeTrace ceq g s).steps =
      (nullC ceq g).2 +
      (epsUnitC ceq g (normalizeTrace ceq g s).null).2 +
      (unitClosureC ceq g.states (normalizeTrace ceq g s).eunit).2 +
      (unitFreeTermC ceq g.term (normalizeTrace ceq g s).ureach).2 +
      (unitFreeBinC ceq g.bin (normalizeTrace ceq g s).ureach).2 +
      (prodRulesC (normalizeTrace ceq g s).uterm (normalizeTrace ceq g s).ubin).2 +
      (hornC ceq g.states (prodRulesC (normalizeTrace ceq g s).uterm
        (normalizeTrace ceq g s).ubin).1).2 +
      (prodBinC ceq (normalizeTrace ceq g s).prod (normalizeTrace ceq g s).ubin).2 +
      (reachRulesC s (normalizeTrace ceq g s).pbin).2 +
      (hornC ceq g.states (reachRulesC s (normalizeTrace ceq g s).pbin).1).2 +
      (outTermC ceq (normalizeTrace ceq g s).reach (normalizeTrace ceq g s).uterm).2 +
      (outBinC ceq (normalizeTrace ceq g s).reach (normalizeTrace ceq g s).pbin).2 +
      (memC ceq s (normalizeTrace ceq g s).prod).2 +
      (memC ceq s (normalizeTrace ceq g s).null).2 + 1 := rfl

end TraceFields

section Specs

variable {S : Type u} {α : Type v} [DecidableEq S]
variable {ceq : S → S → Bool × Nat} (hc : CeqCorrect ceq)

/-- Every rule of a front-end code mentions only listed states. -/
structure WF (g : FrontCode S α) : Prop where
  term : ∀ t, t ∈ g.term → t.1 ∈ g.states
  bin : ∀ t, t ∈ g.bin → t.1 ∈ g.states ∧ t.2.1 ∈ g.states ∧ t.2.2 ∈ g.states
  unit : ∀ p, p ∈ g.unit → p.1 ∈ g.states ∧ p.2 ∈ g.states
  eps : ∀ x, x ∈ g.eps → x ∈ g.states

omit [DecidableEq S] in
/-- A derivable atom is the head of a rule. -/
theorem hornDerivable_head {rules : List (S × List S)} {x : S}
    (h : HornDerivable rules x) : ∃ body, (x, body) ∈ rules := by
  cases h with
  | rule hm _ => exact ⟨_, hm⟩

include hc

/-! #### nullable -/

theorem mem_nullC {g : FrontCode S α} (hwf : WF g) (x : S) :
    x ∈ (nullC ceq g).1 ↔ HornDerivable (nullRules g) x := by
  show x ∈ (hornC ceq g.states (nullRulesC g).1).1 ↔ _
  rw [nullRulesC_fst]
  apply mem_hornC_iff hc
  intro y body hm
  simp only [nullRules, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨z, hz, he⟩ | ⟨p, hp, he⟩ | ⟨t, ht, he⟩
  · cases he; exact hwf.eps _ hz
  · cases he; exact (hwf.unit _ hp).1
  · cases he; exact (hwf.bin _ ht).1

theorem nullC_sub {g : FrontCode S α} (hwf : WF g) (x : S)
    (hx : x ∈ (nullC ceq g).1) : x ∈ g.states := by
  obtain ⟨body, hm⟩ := hornDerivable_head ((mem_nullC hc hwf x).mp hx)
  simp only [nullRules, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨z, hz, he⟩ | ⟨p, hp, he⟩ | ⟨t, ht, he⟩
  · cases he; exact hwf.eps _ hz
  · cases he; exact (hwf.unit _ hp).1
  · cases he; exact (hwf.bin _ ht).1

/-! #### ε-elimination -/

theorem mem_dropLeftC (null : List S) (p : S × S) :
    ∀ bin : List (S × S × S),
      p ∈ (dropLeftC ceq null bin).1 ↔ ∃ y, (p.1, y, p.2) ∈ bin ∧ y ∈ null
  | [] => by simp [dropLeftC]
  | t :: ts => by
      have ih := mem_dropLeftC null p ts
      by_cases h : t.2.1 ∈ null
      · have hb : (memC ceq t.2.1 null).1 = true := by rw [memC_fst hc]; simpa using h
        have hh : (dropLeftC ceq null (t :: ts)).1 = (t.1, t.2.2) :: (dropLeftC ceq null ts).1 := by
          simp [dropLeftC, hb]
        rw [hh, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨y, hy, hn⟩)
          · exact ⟨t.2.1, by simp, h⟩
          · exact ⟨y, List.mem_cons_of_mem _ hy, hn⟩
        · rintro ⟨y, hy, hn⟩
          rcases List.mem_cons.mp hy with he | hy
          · left; rw [← he]
          · right; exact ⟨y, hy, hn⟩
      · have hb : (memC ceq t.2.1 null).1 = false := by rw [memC_fst hc]; simpa using h
        have hh : (dropLeftC ceq null (t :: ts)).1 = (dropLeftC ceq null ts).1 := by
          simp [dropLeftC, hb]
        rw [hh, ih]
        constructor
        · rintro ⟨y, hy, hn⟩; exact ⟨y, List.mem_cons_of_mem _ hy, hn⟩
        · rintro ⟨y, hy, hn⟩
          rcases List.mem_cons.mp hy with he | hy
          · exact absurd (by rw [← he]; exact hn) h
          · exact ⟨y, hy, hn⟩

theorem mem_dropRightC (null : List S) (p : S × S) :
    ∀ bin : List (S × S × S),
      p ∈ (dropRightC ceq null bin).1 ↔ ∃ y, (p.1, p.2, y) ∈ bin ∧ y ∈ null
  | [] => by simp [dropRightC]
  | t :: ts => by
      have ih := mem_dropRightC null p ts
      by_cases h : t.2.2 ∈ null
      · have hb : (memC ceq t.2.2 null).1 = true := by rw [memC_fst hc]; simpa using h
        have hh : (dropRightC ceq null (t :: ts)).1 =
            (t.1, t.2.1) :: (dropRightC ceq null ts).1 := by
          simp [dropRightC, hb]
        rw [hh, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨y, hy, hn⟩)
          · exact ⟨t.2.2, by simp, h⟩
          · exact ⟨y, List.mem_cons_of_mem _ hy, hn⟩
        · rintro ⟨y, hy, hn⟩
          rcases List.mem_cons.mp hy with he | hy
          · left; rw [← he]
          · right; exact ⟨y, hy, hn⟩
      · have hb : (memC ceq t.2.2 null).1 = false := by rw [memC_fst hc]; simpa using h
        have hh : (dropRightC ceq null (t :: ts)).1 = (dropRightC ceq null ts).1 := by
          simp [dropRightC, hb]
        rw [hh, ih]
        constructor
        · rintro ⟨y, hy, hn⟩; exact ⟨y, List.mem_cons_of_mem _ hy, hn⟩
        · rintro ⟨y, hy, hn⟩
          rcases List.mem_cons.mp hy with he | hy
          · exact absurd (by rw [← he]; exact hn) h
          · exact ⟨y, hy, hn⟩

theorem mem_epsUnitC (g : FrontCode S α) (null : List S) (p : S × S) :
    p ∈ (epsUnitC ceq g null).1 ↔
      p ∈ g.unit ∨ (∃ y, (p.1, y, p.2) ∈ g.bin ∧ y ∈ null) ∨
        (∃ y, (p.1, p.2, y) ∈ g.bin ∧ y ∈ null) := by
  show p ∈ (appendC g.unit (appendC (dropLeftC ceq null g.bin).1
      (dropRightC ceq null g.bin).1).1).1 ↔ _
  rw [appendC_fst, appendC_fst, List.mem_append, List.mem_append,
    mem_dropLeftC hc, mem_dropRightC hc]

theorem epsUnitC_wf {g : FrontCode S α} (hwf : WF g) (null : List S) (p : S × S)
    (hp : p ∈ (epsUnitC ceq g null).1) : p.1 ∈ g.states ∧ p.2 ∈ g.states := by
  rcases (mem_epsUnitC hc g null p).mp hp with h | ⟨y, hy, _⟩ | ⟨y, hy, _⟩
  · exact hwf.unit p h
  · have := hwf.bin _ hy; exact ⟨this.1, this.2.2⟩
  · have := hwf.bin _ hy; exact ⟨this.1, this.2.1⟩

/-! #### unit closure -/

theorem reachFromC_fst (states : List S) (eunit : List (S × S)) (x : S) :
    (reachFromC ceq states eunit x).1 =
      (hornC ceq states (unitRulesFrom eunit x)).1.map (fun z => (x, z)) := by
  simp [reachFromC, unitRulesFrom, mapC_fst]

theorem mem_unitClosureC (states : List S) (eunit : List (S × S))
    (heu : ∀ p, p ∈ eunit → p.1 ∈ states ∧ p.2 ∈ states) (x z : S) :
    (x, z) ∈ (unitClosureC ceq states eunit).1 ↔
      x ∈ states ∧ HornDerivable (unitRulesFrom eunit x) z := by
  unfold unitClosureC
  rw [mem_forListC]
  constructor
  · rintro ⟨b, hb, hm⟩
    rw [reachFromC_fst hc, List.mem_map] at hm
    obtain ⟨z', hz', he⟩ := hm
    cases he
    refine ⟨hb, ?_⟩
    refine (mem_hornC_iff hc states _ ?_ z).mp hz'
    intro y body hm
    simp only [unitRulesFrom, List.mem_cons, List.mem_map] at hm
    rcases hm with he | ⟨p, hp, he⟩
    · cases he; exact hb
    · cases he; exact (heu p hp).2
  · rintro ⟨hx, hd⟩
    refine ⟨x, hx, ?_⟩
    rw [reachFromC_fst hc, List.mem_map]
    refine ⟨z, ?_, rfl⟩
    refine (mem_hornC_iff hc states _ ?_ z).mpr hd
    intro y body hm
    simp only [unitRulesFrom, List.mem_cons, List.mem_map] at hm
    rcases hm with he | ⟨p, hp, he⟩
    · cases he; exact hx
    · cases he; exact (heu p hp).2

/-! #### unit elimination -/

theorem mem_copyTermC (term : List (S × α)) (p : S × S) (q : S × α) :
    q ∈ (copyTermC ceq term p).1 ↔ q.1 = p.1 ∧ (p.2, q.2) ∈ term := by
  unfold copyTermC
  rw [mem_forListC]
  constructor
  · rintro ⟨r, hr, hm⟩
    by_cases h : p.2 = r.1
    · have hb : (ceq p.2 r.1).1 = true := by rw [hc]; simpa using h
      rw [if_pos hb] at hm
      simp only [List.mem_singleton] at hm
      subst hm
      refine ⟨rfl, ?_⟩
      rw [h]; exact hr
    · have hb : (ceq p.2 r.1).1 = false := by rw [hc]; simpa using h
      rw [if_neg (by simp [hb])] at hm
      simp at hm
  · rintro ⟨h1, h2⟩
    refine ⟨(p.2, q.2), h2, ?_⟩
    have hb : (ceq p.2 p.2).1 = true := by rw [hc]; simp
    simp only [hb, if_true, List.mem_singleton]
    rw [← h1]

theorem mem_copyBinC (bin : List (S × S × S)) (p : S × S) (q : S × S × S) :
    q ∈ (copyBinC ceq bin p).1 ↔ q.1 = p.1 ∧ (p.2, q.2.1, q.2.2) ∈ bin := by
  unfold copyBinC
  rw [mem_forListC]
  constructor
  · rintro ⟨r, hr, hm⟩
    by_cases h : p.2 = r.1
    · have hb : (ceq p.2 r.1).1 = true := by rw [hc]; simpa using h
      rw [if_pos hb] at hm
      simp only [List.mem_singleton] at hm
      subst hm
      refine ⟨rfl, ?_⟩
      rw [h]; exact hr
    · have hb : (ceq p.2 r.1).1 = false := by rw [hc]; simpa using h
      rw [if_neg (by simp [hb])] at hm
      simp at hm
  · rintro ⟨h1, h2⟩
    refine ⟨(p.2, q.2.1, q.2.2), h2, ?_⟩
    have hb : (ceq p.2 p.2).1 = true := by rw [hc]; simp
    simp only [hb, if_true, List.mem_singleton]
    rw [← h1]

theorem mem_unitFreeTermC (term : List (S × α)) (ureach : List (S × S)) (x : S) (a : α) :
    (x, a) ∈ (unitFreeTermC ceq term ureach).1 ↔
      ∃ y, (x, y) ∈ ureach ∧ (y, a) ∈ term := by
  unfold unitFreeTermC
  rw [mem_forListC]
  constructor
  · rintro ⟨p, hp, hm⟩
    rw [mem_copyTermC hc] at hm
    obtain ⟨h1, h2⟩ := hm
    refine ⟨p.2, ?_, h2⟩
    have : p = (x, p.2) := Prod.ext h1.symm rfl
    rw [← this]; exact hp
  · rintro ⟨y, hy, ht⟩
    exact ⟨(x, y), hy, (mem_copyTermC hc term (x, y) (x, a)).mpr ⟨rfl, ht⟩⟩

theorem mem_unitFreeBinC (bin : List (S × S × S)) (ureach : List (S × S)) (x c d : S) :
    (x, c, d) ∈ (unitFreeBinC ceq bin ureach).1 ↔
      ∃ y, (x, y) ∈ ureach ∧ (y, c, d) ∈ bin := by
  unfold unitFreeBinC
  rw [mem_forListC]
  constructor
  · rintro ⟨p, hp, hm⟩
    rw [mem_copyBinC hc] at hm
    obtain ⟨h1, h2⟩ := hm
    refine ⟨p.2, ?_, h2⟩
    have : p = (x, p.2) := Prod.ext h1.symm rfl
    rw [← this]; exact hp
  · rintro ⟨y, hy, ht⟩
    exact ⟨(x, y), hy, (mem_copyBinC hc bin (x, y) (x, c, d)).mpr ⟨rfl, ht⟩⟩

/-! #### productive and reachable states -/

theorem mem_prod (states : List S) (uterm : List (S × α)) (ubin : List (S × S × S))
    (ht : ∀ p, p ∈ uterm → p.1 ∈ states) (hb : ∀ t, t ∈ ubin → t.1 ∈ states) (x : S) :
    x ∈ (hornC ceq states (prodRulesC uterm ubin).1).1 ↔
      HornDerivable (prodRules uterm ubin) x := by
  rw [prodRulesC_fst]
  apply mem_hornC_iff hc
  intro y body hm
  simp only [prodRules, List.mem_append, List.mem_map] at hm
  rcases hm with ⟨p, hp, he⟩ | ⟨t, ht', he⟩
  · cases he; exact ht p hp
  · cases he; exact hb t ht'

theorem mem_prodBinC (prod : List S) (ubin : List (S × S × S)) (t : S × S × S) :
    t ∈ (prodBinC ceq prod ubin).1 ↔
      t ∈ ubin ∧ t.1 ∈ prod ∧ t.2.1 ∈ prod ∧ t.2.2 ∈ prod := by
  unfold prodBinC
  rw [mem_filterC]
  simp [memC_fst hc, and_assoc]

omit hc in
theorem forListC_const_fst {β γ : Type*} (f : β → List γ) (c : Nat) :
    ∀ l : List β, (forListC (fun b => (f b, c)) l).1 = l.flatMap f
  | [] => rfl
  | b :: l => by
      show f b ++ (forListC (fun b => (f b, c)) l).1 = _
      rw [forListC_const_fst f c l]; simp

theorem reachRulesC_fst (s : S) (pbin : List (S × S × S)) :
    (reachRulesC s pbin).1 = reachRules s pbin := by
  show (s, []) :: (forListC (fun t : S × S × S =>
      ([(t.2.1, [t.1]), (t.2.2, [t.1])], 5)) pbin).1 = _
  rw [forListC_const_fst]; rfl

theorem mem_reach (states : List S) (s : S) (pbin : List (S × S × S))
    (hs : s ∈ states) (hb : ∀ t, t ∈ pbin → t.2.1 ∈ states ∧ t.2.2 ∈ states) (x : S) :
    x ∈ (hornC ceq states (reachRulesC s pbin).1).1 ↔
      HornDerivable (reachRules s pbin) x := by
  rw [reachRulesC_fst hc]
  apply mem_hornC_iff hc
  intro y body hm
  simp only [reachRules, List.mem_cons, List.mem_flatMap] at hm
  rcases hm with he | ⟨t, ht, hm⟩
  · cases he; exact hs
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
    rcases hm with he | he
    · cases he; exact (hb t ht).1
    · cases he; exact (hb t ht).2

theorem mem_outTermC (reach : List S) (uterm : List (S × α)) (p : S × α) :
    p ∈ (outTermC ceq reach uterm).1 ↔ p ∈ uterm ∧ p.1 ∈ reach := by
  unfold outTermC
  rw [mem_filterC]
  simp [memC_fst hc]

theorem mem_outBinC (reach : List S) (pbin : List (S × S × S)) (t : S × S × S) :
    t ∈ (outBinC ceq reach pbin).1 ↔ t ∈ pbin ∧ t.1 ∈ reach := by
  unfold outBinC
  rw [mem_filterC]
  simp [memC_fst hc]

end Specs


section Costs

variable {S : Type u} {α : Type v} [DecidableEq S]
variable {ceq : S → S → Bool × Nat}

/-- Size hypothesis: every list of the front-end code has length at most `m`. -/
structure SizeBound (g : FrontCode S α) (m : Nat) : Prop where
  states : g.states.length ≤ m
  term : g.term.length ≤ m
  bin : g.bin.length ≤ m
  unit : g.unit.length ≤ m
  eps : g.eps.length ≤ m

omit [DecidableEq S] in
theorem sum_map_const_eq {β : Type*} (l : List β) (c : Nat) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]; ring

omit [DecidableEq S] in
theorem bodySize_append (l₁ l₂ : List (S × List S)) :
    bodySize (l₁ ++ l₂) = bodySize l₁ + bodySize l₂ := by
  simp [bodySize]

omit [DecidableEq S] in
theorem bodySize_map {β : Type*} (l : List β) (f : β → S) (g : β → List S) (c : Nat)
    (hg : ∀ b, (g b).length = c) :
    bodySize (l.map (fun b => (f b, g b))) = l.length * c := by
  unfold bodySize
  rw [List.map_map]
  have : ((fun r : S × List S => r.2.length) ∘ fun b => (f b, g b)) = fun _ => c := by
    funext b; simp [hg]
  rw [this, sum_map_const_eq]

theorem nullRulesC_snd (g : FrontCode S α) :
    (nullRulesC g).2 = 5 * g.eps.length + 5 * g.unit.length + 4 * g.bin.length + 5 := by
  simp only [nullRulesC, mapC_snd, appendC_snd, mapC_fst, List.length_map]
  ring

theorem nullRules_length (g : FrontCode S α) :
    (nullRules g).length = g.eps.length + g.unit.length + g.bin.length := by
  simp [nullRules]; omega

theorem nullRules_bodySize (g : FrontCode S α) :
    bodySize (nullRules g) = g.unit.length + 2 * g.bin.length := by
  unfold nullRules
  rw [bodySize_append, bodySize_append,
    bodySize_map _ _ _ 0 (fun _ => rfl), bodySize_map _ _ _ 1 (fun _ => rfl),
    bodySize_map _ _ _ 2 (fun _ => rfl)]
  ring

variable {E : Nat}

/-- Membership cost bound on lists of states. -/
theorem memC_le_states {g : FrontCode S α} (hb : CeqBound ceq (· ∈ g.states) E)
    {m : Nat} (x : S) (hx : x ∈ g.states) (l : List S) (hl : ∀ y, y ∈ l → y ∈ g.states)
    (hlm : l.length ≤ m) : (memC ceq x l).2 ≤ m * (E + 1) + 1 :=
  memC_snd_le' hb x hx l hl hlm

theorem dropLeftC_bound {g : FrontCode S α} (hb : CeqBound ceq (· ∈ g.states) E)
    {m : Nat} (null : List S) (hn : ∀ y, y ∈ null → y ∈ g.states) (hnm : null.length ≤ m) :
    ∀ bin : List (S × S × S), (∀ t, t ∈ bin → t.2.1 ∈ g.states) →
      (dropLeftC ceq null bin).1.length ≤ bin.length ∧
      (dropLeftC ceq null bin).2 ≤ bin.length * (m * (E + 1) + 3) + 1
  | [], _ => by simp [dropLeftC]
  | t :: ts, ht => by
      obtain ⟨ih1, ih2⟩ := dropLeftC_bound hb null hn hnm ts
        (fun t' h' => ht t' (List.mem_cons_of_mem _ h'))
      have h1 := memC_le_states hb t.2.1 (ht t (by simp)) null hn hnm
      have e : (ts.length + 1) * (m * (E + 1) + 3) =
          ts.length * (m * (E + 1) + 3) + m * (E + 1) + 3 := by ring
      unfold dropLeftC
      split_ifs
      · simp only [List.length_cons]; rw [e]; omega
      · simp only [List.length_cons]; rw [e]; omega

theorem dropRightC_bound {g : FrontCode S α} (hb : CeqBound ceq (· ∈ g.states) E)
    {m : Nat} (null : List S) (hn : ∀ y, y ∈ null → y ∈ g.states) (hnm : null.length ≤ m) :
    ∀ bin : List (S × S × S), (∀ t, t ∈ bin → t.2.2 ∈ g.states) →
      (dropRightC ceq null bin).1.length ≤ bin.length ∧
      (dropRightC ceq null bin).2 ≤ bin.length * (m * (E + 1) + 3) + 1
  | [], _ => by simp [dropRightC]
  | t :: ts, ht => by
      obtain ⟨ih1, ih2⟩ := dropRightC_bound hb null hn hnm ts
        (fun t' h' => ht t' (List.mem_cons_of_mem _ h'))
      have h1 := memC_le_states hb t.2.2 (ht t (by simp)) null hn hnm
      have e : (ts.length + 1) * (m * (E + 1) + 3) =
          ts.length * (m * (E + 1) + 3) + m * (E + 1) + 3 := by ring
      unfold dropRightC
      split_ifs
      · simp only [List.length_cons]; rw [e]; omega
      · simp only [List.length_cons]; rw [e]; omega


/-! #### Atom facts used by the cost analysis -/

omit [DecidableEq S] in
theorem nullRules_atoms {g : FrontCode S α} (hwf : WF g) :
    ∀ r, r ∈ nullRules g → r.1 ∈ g.states ∧ ∀ y, y ∈ r.2 → y ∈ g.states := by
  intro r hr
  simp only [nullRules, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨z, hz, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨t, ht, rfl⟩
  · exact ⟨hwf.eps _ hz, by simp⟩
  · exact ⟨(hwf.unit _ hp).1, by simpa using (hwf.unit _ hp).2⟩
  · have := hwf.bin _ ht
    exact ⟨this.1, by simpa using this.2⟩

omit [DecidableEq S] in
theorem unitRulesFrom_atoms (states : List S) (eunit : List (S × S))
    (heu : ∀ p, p ∈ eunit → p.1 ∈ states ∧ p.2 ∈ states) (x : S) (hx : x ∈ states) :
    ∀ r, r ∈ unitRulesFrom eunit x → r.1 ∈ states ∧ ∀ y, y ∈ r.2 → y ∈ states := by
  intro r hr
  simp only [unitRulesFrom, List.mem_cons, List.mem_map] at hr
  rcases hr with rfl | ⟨p, hp, rfl⟩
  · exact ⟨hx, by simp⟩
  · exact ⟨(heu p hp).2, by simpa using (heu p hp).1⟩

omit [DecidableEq S] in
theorem prodRules_atoms (states : List S) (uterm : List (S × α)) (ubin : List (S × S × S))
    (ht : ∀ p, p ∈ uterm → p.1 ∈ states)
    (hb : ∀ t, t ∈ ubin → t.1 ∈ states ∧ t.2.1 ∈ states ∧ t.2.2 ∈ states) :
    ∀ r, r ∈ prodRules uterm ubin → r.1 ∈ states ∧ ∀ y, y ∈ r.2 → y ∈ states := by
  intro r hr
  simp only [prodRules, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨p, hp, rfl⟩ | ⟨t, ht', rfl⟩
  · exact ⟨ht p hp, by simp⟩
  · have := hb t ht'
    exact ⟨this.1, by simpa using this.2⟩

omit [DecidableEq S] in
theorem reachRules_atoms (states : List S) (s : S) (pbin : List (S × S × S)) (hs : s ∈ states)
    (hb : ∀ t, t ∈ pbin → t.1 ∈ states ∧ t.2.1 ∈ states ∧ t.2.2 ∈ states) :
    ∀ r, r ∈ reachRules s pbin → r.1 ∈ states ∧ ∀ y, y ∈ r.2 → y ∈ states := by
  intro r hr
  simp only [reachRules, List.mem_cons, List.mem_flatMap] at hr
  rcases hr with rfl | ⟨t, ht, hm⟩
  · exact ⟨hs, by simp⟩
  · have := hb t ht
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact ⟨this.2.1, by simpa using this.1⟩
    · exact ⟨this.2.2, by simpa using this.1⟩

omit [DecidableEq S] in
theorem reachRules_length (s : S) (pbin : List (S × S × S)) :
    (reachRules s pbin).length = 2 * pbin.length + 1 := by
  unfold reachRules
  induction pbin with
  | nil => simp
  | cons t ts ih => simp at ih ⊢; omega

omit [DecidableEq S] in
theorem reachRules_bodySize (s : S) (pbin : List (S × S × S)) :
    bodySize (reachRules s pbin) = 2 * pbin.length := by
  unfold reachRules bodySize
  induction pbin with
  | nil => simp
  | cons t ts ih => simp at ih ⊢; omega

omit [DecidableEq S] in
theorem prodRules_length (uterm : List (S × α)) (ubin : List (S × S × S)) :
    (prodRules uterm ubin).length = uterm.length + ubin.length := by
  simp [prodRules]

omit [DecidableEq S] in
theorem prodRules_bodySize (uterm : List (S × α)) (ubin : List (S × S × S)) :
    bodySize (prodRules uterm ubin) = 2 * ubin.length := by
  unfold prodRules
  rw [bodySize_append, bodySize_map _ _ _ 0 (fun _ => rfl), bodySize_map _ _ _ 2 (fun _ => rfl)]
  ring

omit [DecidableEq S] in
theorem unitRulesFrom_length (eunit : List (S × S)) (x : S) :
    (unitRulesFrom eunit x).length = eunit.length + 1 := by
  simp [unitRulesFrom]

omit [DecidableEq S] in
theorem unitRulesFrom_bodySize (eunit : List (S × S)) (x : S) :
    bodySize (unitRulesFrom eunit x) = eunit.length := by
  unfold unitRulesFrom
  rw [show (x, ([] : List S)) :: eunit.map (fun p => (p.2, [p.1])) =
      [(x, ([] : List S))] ++ eunit.map (fun p => (p.2, [p.1])) from rfl,
    bodySize_append, bodySize_map _ _ _ 1 (fun _ => rfl)]
  simp [bodySize]


/-! #### Value facts of the trace -/

section TraceValues

variable {g : FrontCode S α} {m : Nat} (s : S)
  (hc : CeqCorrect ceq) (hwf : WF g) (hsz : SizeBound g m)
  (hb : CeqBound ceq (· ∈ g.states) E) (hs : s ∈ g.states)

include hc hwf hsz hb in
theorem trace_null_facts :
    (∀ y, y ∈ (normalizeTrace ceq g s).null → y ∈ g.states) ∧
    (normalizeTrace ceq g s).null.length ≤ m := by
  refine ⟨nullC_sub hc hwf, ?_⟩
  rw [trace_null]
  show (hornC ceq g.states (nullRulesC g).1).1.length ≤ m
  rw [nullRulesC_fst]
  exact le_trans (hornC_length_le hb _ _ (fun y h => h)
    (fun r hr => (nullRules_atoms hwf r hr).1)
    (fun r hr => (nullRules_atoms hwf r hr).2)) hsz.states

include hc hwf hsz hb in
theorem trace_eunit_facts :
    (∀ p, p ∈ (normalizeTrace ceq g s).eunit → p.1 ∈ g.states ∧ p.2 ∈ g.states) ∧
    (normalizeTrace ceq g s).eunit.length ≤ 3 * m := by
  refine ⟨fun p hp => epsUnitC_wf hc hwf _ p hp, ?_⟩
  obtain ⟨hn1, hn2⟩ := trace_null_facts s hc hwf hsz hb
  rw [trace_eunit]
  show (appendC g.unit (appendC (dropLeftC ceq _ g.bin).1
      (dropRightC ceq _ g.bin).1).1).1.length ≤ _
  rw [appendC_fst, appendC_fst, List.length_append, List.length_append]
  have h1 := (dropLeftC_bound hb _ hn1 hn2 g.bin (fun t ht => (hwf.bin t ht).2.1)).1
  have h2 := (dropRightC_bound hb _ hn1 hn2 g.bin (fun t ht => (hwf.bin t ht).2.2)).1
  have := hsz.unit; have := hsz.bin
  omega

include hc hwf hsz hb in
theorem trace_ureach_facts :
    (∀ p, p ∈ (normalizeTrace ceq g s).ureach → p.1 ∈ g.states ∧ p.2 ∈ g.states) ∧
    (normalizeTrace ceq g s).ureach.length ≤ m * m := by
  obtain ⟨he1, _⟩ := trace_eunit_facts s hc hwf hsz hb
  constructor
  · intro p hp
    rw [trace_ureach] at hp
    have hp' : (p.1, p.2) ∈ (unitClosureC ceq g.states (normalizeTrace ceq g s).eunit).1 := hp
    obtain ⟨hx, hd⟩ := (mem_unitClosureC hc _ _ he1 p.1 p.2).mp hp'
    obtain ⟨body, hm⟩ := hornDerivable_head hd
    exact ⟨hx, (unitRulesFrom_atoms _ _ he1 p.1 hx _ hm).1⟩
  · rw [trace_ureach]
    unfold unitClosureC
    refine le_trans (forListC_length_le _ m _ ?_) (Nat.mul_le_mul_right _ hsz.states)
    intro x hx
    rw [reachFromC_fst hc, List.length_map]
    exact le_trans (hornC_length_le hb _ _ (fun y h => h)
      (fun r hr => (unitRulesFrom_atoms _ _ he1 x hx r hr).1)
      (fun r hr => (unitRulesFrom_atoms _ _ he1 x hx r hr).2)) hsz.states

include hc hwf hsz hb in
theorem trace_uterm_facts :
    (∀ p, p ∈ (normalizeTrace ceq g s).uterm → p.1 ∈ g.states) ∧
    (normalizeTrace ceq g s).uterm.length ≤ m * m * m := by
  obtain ⟨hr1, hr2⟩ := trace_ureach_facts s hc hwf hsz hb
  constructor
  · intro p hp
    rw [trace_uterm] at hp
    have hp' : (p.1, p.2) ∈ (unitFreeTermC ceq g.term (normalizeTrace ceq g s).ureach).1 := hp
    obtain ⟨y, hy, _⟩ := (mem_unitFreeTermC hc _ _ p.1 p.2).mp hp'
    exact (hr1 _ hy).1
  · rw [trace_uterm]
    unfold unitFreeTermC
    refine le_trans (forListC_length_le _ m _ ?_) (Nat.mul_le_mul_right _ hr2)
    intro p _
    unfold copyTermC
    refine le_trans (forListC_length_le _ 1 _ ?_) (by have := hsz.term; omega)
    intro q _
    split_ifs <;> simp

include hc hwf hsz hb in
theorem trace_ubin_facts :
    (∀ t, t ∈ (normalizeTrace ceq g s).ubin →
      t.1 ∈ g.states ∧ t.2.1 ∈ g.states ∧ t.2.2 ∈ g.states) ∧
    (normalizeTrace ceq g s).ubin.length ≤ m * m * m := by
  obtain ⟨hr1, hr2⟩ := trace_ureach_facts s hc hwf hsz hb
  constructor
  · intro t ht
    rw [trace_ubin] at ht
    have ht' : (t.1, t.2.1, t.2.2) ∈ (unitFreeBinC ceq g.bin (normalizeTrace ceq g s).ureach).1 :=
      ht
    obtain ⟨y, hy, hbin⟩ := (mem_unitFreeBinC hc _ _ t.1 t.2.1 t.2.2).mp ht'
    have := hwf.bin _ hbin
    exact ⟨(hr1 _ hy).1, this.2.1, this.2.2⟩
  · rw [trace_ubin]
    unfold unitFreeBinC
    refine le_trans (forListC_length_le _ m _ ?_) (Nat.mul_le_mul_right _ hr2)
    intro p _
    unfold copyBinC
    refine le_trans (forListC_length_le _ 1 _ ?_) (by have := hsz.bin; omega)
    intro q _
    split_ifs <;> simp

include hc hwf hsz hb in
theorem trace_prod_facts :
    (∀ y, y ∈ (normalizeTrace ceq g s).prod → y ∈ g.states) ∧
    (normalizeTrace ceq g s).prod.length ≤ m := by
  obtain ⟨ht1, _⟩ := trace_uterm_facts s hc hwf hsz hb
  obtain ⟨hb1, _⟩ := trace_ubin_facts s hc hwf hsz hb
  rw [trace_prod, prodRulesC_fst]
  have hat := prodRules_atoms g.states _ _ ht1 hb1
  exact ⟨hornC_sub_dom hb _ _ (fun y h => h) (fun r hr => (hat r hr).1)
      (fun r hr => (hat r hr).2),
    le_trans (hornC_length_le hb _ _ (fun y h => h) (fun r hr => (hat r hr).1)
      (fun r hr => (hat r hr).2)) hsz.states⟩

include hc hwf hsz hb in
theorem trace_pbin_facts :
    (∀ t, t ∈ (normalizeTrace ceq g s).pbin →
      t.1 ∈ g.states ∧ t.2.1 ∈ g.states ∧ t.2.2 ∈ g.states) ∧
    (normalizeTrace ceq g s).pbin.length ≤ m * m * m := by
  obtain ⟨hb1, hb2⟩ := trace_ubin_facts s hc hwf hsz hb
  rw [trace_pbin]
  refine ⟨fun t ht => hb1 t ((mem_prodBinC hc _ _ t).mp ht).1, ?_⟩
  exact le_trans (filterC_length_le _ _) hb2

include hc hwf hsz hb hs in
theorem trace_reach_facts :
    (∀ y, y ∈ (normalizeTrace ceq g s).reach → y ∈ g.states) ∧
    (normalizeTrace ceq g s).reach.length ≤ m := by
  obtain ⟨hp1, _⟩ := trace_pbin_facts s hc hwf hsz hb
  rw [trace_reach, reachRulesC_fst hc]
  have hat := reachRules_atoms g.states s _ hs hp1
  exact ⟨hornC_sub_dom hb _ _ (fun y h => h) (fun r hr => (hat r hr).1)
      (fun r hr => (hat r hr).2),
    le_trans (hornC_length_le hb _ _ (fun y h => h) (fun r hr => (hat r hr).1)
      (fun r hr => (hat r hr).2)) hsz.states⟩

end TraceValues


/-! #### Stage costs -/

theorem powX_mono (m E a b : Nat) (h : a ≤ b) :
    (m + 1) ^ a * (E + 1) ≤ (m + 1) ^ b * (E + 1) :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) h)

theorem one_le_powX (m E a : Nat) : 1 ≤ (m + 1) ^ a * (E + 1) :=
  Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))

theorem lin_le_powX (m E a : Nat) (ha : 1 ≤ a) : m + 1 ≤ (m + 1) ^ a * (E + 1) := by
  calc m + 1 = (m + 1) ^ 1 := (pow_one _).symm
    _ ≤ (m + 1) ^ a := Nat.pow_le_pow_right (by omega) ha
    _ ≤ (m + 1) ^ a * (E + 1) := Nat.le_mul_of_pos_right _ (by omega)

section StageCosts

variable {g : FrontCode S α} {m : Nat} (s : S)
  (hc : CeqCorrect ceq) (hwf : WF g) (hsz : SizeBound g m)
  (hb : CeqBound ceq (· ∈ g.states) E) (hs : s ∈ g.states)

include hwf hsz hb in
theorem cost_null : (nullC ceq g).2 ≤ 63 * ((m + 1) ^ 3 * (E + 1)) := by
  show (nullRulesC g).2 + (hornC ceq g.states (nullRulesC g).1).2 + 1 ≤ _
  rw [nullRulesC_snd, nullRulesC_fst]
  have h1 := hornC_cost_le hb g.states (nullRules g) (fun y h => h)
    (fun r hr => (nullRules_atoms hwf r hr).1) (fun r hr => (nullRules_atoms hwf r hr).2)
  have hRM : ruleMeasure (nullRules g) ≤ 6 * m + 1 := by
    unfold ruleMeasure; rw [nullRules_length, nullRules_bodySize]
    have := hsz.eps; have := hsz.unit; have := hsz.bin; omega
  have hst := hsz.states
  have h2 : 8 * (g.states.length + 1) ^ 2 * ruleMeasure (nullRules g) * (E + 1) ≤
      48 * ((m + 1) ^ 3 * (E + 1)) :=
    calc 8 * (g.states.length + 1) ^ 2 * ruleMeasure (nullRules g) * (E + 1)
        ≤ 8 * (m + 1) ^ 2 * (6 * (m + 1)) * (E + 1) := by gcongr <;> omega
      _ = 48 * ((m + 1) ^ 3 * (E + 1)) := by ring
  have h3 := lin_le_powX m E 3 (by omega)
  have := hsz.eps; have := hsz.unit; have := hsz.bin
  omega

include hc hwf hsz hb in
theorem cost_eps :
    (epsUnitC ceq g (normalizeTrace ceq g s).null).2 ≤ 14 * ((m + 1) ^ 2 * (E + 1)) := by
  obtain ⟨hn1, hn2⟩ := trace_null_facts s hc hwf hsz hb
  show (dropLeftC ceq _ g.bin).2 + (dropRightC ceq _ g.bin).2 +
      (appendC (dropLeftC ceq _ g.bin).1 (dropRightC ceq _ g.bin).1).2 +
      (appendC g.unit (appendC (dropLeftC ceq _ g.bin).1 (dropRightC ceq _ g.bin).1).1).2 ≤ _
  rw [appendC_snd, appendC_snd]
  obtain ⟨h1, h2⟩ := dropLeftC_bound hb _ hn1 hn2 g.bin (fun t ht => (hwf.bin t ht).2.1)
  obtain ⟨_, h4⟩ := dropRightC_bound hb _ hn1 hn2 g.bin (fun t ht => (hwf.bin t ht).2.2)
  have hB := hsz.bin; have hU := hsz.unit
  have h5 : g.bin.length * (m * (E + 1) + 3) ≤ 4 * ((m + 1) ^ 2 * (E + 1)) := by
    have hi : m * (E + 1) + 3 ≤ 4 * ((m + 1) * (E + 1)) := by nlinarith
    calc g.bin.length * (m * (E + 1) + 3) ≤ (m + 1) * (4 * ((m + 1) * (E + 1))) :=
          Nat.mul_le_mul (by omega) hi
      _ = 4 * ((m + 1) ^ 2 * (E + 1)) := by ring
  have h6 := lin_le_powX m E 2 (by omega)
  omega

theorem reachFromC_snd (states : List S) (eunit : List (S × S)) (x : S) :
    (reachFromC ceq states eunit x).2 =
      4 * eunit.length + 1 + (hornC ceq states (unitRulesFrom eunit x)).2 +
        (4 * (hornC ceq states (unitRulesFrom eunit x)).1.length + 1) + 1 := by
  simp only [reachFromC, mapC_snd, mapC_fst, unitRulesFrom]

include hc hwf hsz hb in
theorem cost_unitClosure :
    (unitClosureC ceq g.states (normalizeTrace ceq g s).eunit).2 ≤
      134 * ((m + 1) ^ 4 * (E + 1)) := by
  obtain ⟨he1, he2⟩ := trace_eunit_facts s hc hwf hsz hb
  have hst := hsz.states
  have hper : ∀ x, x ∈ g.states →
      (reachFromC ceq g.states (normalizeTrace ceq g s).eunit x).1.length ≤
        (reachFromC ceq g.states (normalizeTrace ceq g s).eunit x).2 ∧
      (reachFromC ceq g.states (normalizeTrace ceq g s).eunit x).2 ≤
        66 * ((m + 1) ^ 3 * (E + 1)) := by
    intro x hx
    have hat := unitRulesFrom_atoms g.states _ he1 x hx
    have h1 := hornC_cost_le hb g.states (unitRulesFrom (normalizeTrace ceq g s).eunit x)
      (fun y h => h) (fun r hr => (hat r hr).1) (fun r hr => (hat r hr).2)
    have h2 := hornC_length_le hb g.states (unitRulesFrom (normalizeTrace ceq g s).eunit x)
      (fun y h => h) (fun r hr => (hat r hr).1) (fun r hr => (hat r hr).2)
    have hRM : ruleMeasure (unitRulesFrom (normalizeTrace ceq g s).eunit x) ≤ 6 * m + 2 := by
      unfold ruleMeasure; rw [unitRulesFrom_length, unitRulesFrom_bodySize]; omega
    have h3 : 8 * (g.states.length + 1) ^ 2 *
        ruleMeasure (unitRulesFrom (normalizeTrace ceq g s).eunit x) * (E + 1) ≤
        48 * ((m + 1) ^ 3 * (E + 1)) :=
      calc _ ≤ 8 * (m + 1) ^ 2 * (6 * (m + 1)) * (E + 1) := by gcongr <;> omega
        _ = 48 * ((m + 1) ^ 3 * (E + 1)) := by ring
    have h4 := lin_le_powX m E 3 (by omega)
    rw [reachFromC_fst hc, List.length_map, reachFromC_snd]
    constructor
    · omega
    · omega
  unfold unitClosureC
  obtain ⟨_, h⟩ := forListC_bound_const _ _ g.states hper
  have h5 : g.states.length * (2 * (66 * ((m + 1) ^ 3 * (E + 1))) + 1) ≤
      133 * ((m + 1) ^ 4 * (E + 1)) := by
    have h6 := one_le_powX m E 3
    calc _ ≤ (m + 1) * (133 * ((m + 1) ^ 3 * (E + 1))) := by gcongr <;> omega
      _ = 133 * ((m + 1) ^ 4 * (E + 1)) := by ring
  have h7 := one_le_powX m E 4
  omega

include hc hwf hsz hb in
theorem cost_copyTerm (p : S × S) (hp : p.2 ∈ g.states) :
    (copyTermC ceq g.term p).1.length ≤ (copyTermC ceq g.term p).2 ∧
    (copyTermC ceq g.term p).2 ≤ 4 * ((m + 1) * (E + 1)) := by
  unfold copyTermC
  have := forListC_bound_const (fun q : S × α =>
    if (ceq p.2 q.1).1 then ([(p.1, q.2)], (ceq p.2 q.1).2 + 1)
    else ([], (ceq p.2 q.1).2 + 1)) (E + 1) g.term (by
      intro q hq
      have := hb p.2 q.1 hp (hwf.term q hq)
      split_ifs <;> simp <;> omega)
  refine ⟨this.1, le_trans this.2 ?_⟩
  have hT := hsz.term
  calc g.term.length * (2 * (E + 1) + 1) + 1 ≤ m * (3 * (E + 1)) + (E + 1) := by
        gcongr <;> omega
    _ ≤ 4 * ((m + 1) * (E + 1)) := by nlinarith

include hc hwf hsz hb in
theorem cost_copyBin (p : S × S) (hp : p.2 ∈ g.states) :
    (copyBinC ceq g.bin p).1.length ≤ (copyBinC ceq g.bin p).2 ∧
    (copyBinC ceq g.bin p).2 ≤ 4 * ((m + 1) * (E + 1)) := by
  unfold copyBinC
  have := forListC_bound_const (fun q : S × S × S =>
    if (ceq p.2 q.1).1 then ([(p.1, q.2.1, q.2.2)], (ceq p.2 q.1).2 + 1)
    else ([], (ceq p.2 q.1).2 + 1)) (E + 1) g.bin (by
      intro q hq
      have := hb p.2 q.1 hp (hwf.bin q hq).1
      split_ifs <;> simp <;> omega)
  refine ⟨this.1, le_trans this.2 ?_⟩
  have hB := hsz.bin
  calc g.bin.length * (2 * (E + 1) + 1) + 1 ≤ m * (3 * (E + 1)) + (E + 1) := by
        gcongr <;> omega
    _ ≤ 4 * ((m + 1) * (E + 1)) := by nlinarith

include hc hwf hsz hb in
theorem cost_unitFreeTerm :
    (unitFreeTermC ceq g.term (normalizeTrace ceq g s).ureach).2 ≤
      10 * ((m + 1) ^ 3 * (E + 1)) := by
  obtain ⟨hr1, hr2⟩ := trace_ureach_facts s hc hwf hsz hb
  unfold unitFreeTermC
  obtain ⟨_, h⟩ := forListC_bound_const _ _ _
    (fun p hp => cost_copyTerm hc hwf hsz hb p (hr1 p hp).2)
  have h5 : (normalizeTrace ceq g s).ureach.length * (2 * (4 * ((m + 1) * (E + 1))) + 1) ≤
      9 * ((m + 1) ^ 3 * (E + 1)) := by
    have h6 := one_le_powX m E 1
    calc _ ≤ (m + 1) * (m + 1) * (9 * ((m + 1) * (E + 1))) := by
          gcongr
          · nlinarith
          · rw [pow_one] at h6; omega
      _ = 9 * ((m + 1) ^ 3 * (E + 1)) := by ring
  have h7 := one_le_powX m E 3
  omega

include hc hwf hsz hb in
theorem cost_unitFreeBin :
    (unitFreeBinC ceq g.bin (normalizeTrace ceq g s).ureach).2 ≤
      10 * ((m + 1) ^ 3 * (E + 1)) := by
  obtain ⟨hr1, hr2⟩ := trace_ureach_facts s hc hwf hsz hb
  unfold unitFreeBinC
  obtain ⟨_, h⟩ := forListC_bound_const _ _ _
    (fun p hp => cost_copyBin hc hwf hsz hb p (hr1 p hp).2)
  have h5 : (normalizeTrace ceq g s).ureach.length * (2 * (4 * ((m + 1) * (E + 1))) + 1) ≤
      9 * ((m + 1) ^ 3 * (E + 1)) := by
    have h6 := one_le_powX m E 1
    calc _ ≤ (m + 1) * (m + 1) * (9 * ((m + 1) * (E + 1))) := by
          gcongr
          · nlinarith
          · rw [pow_one] at h6; omega
      _ = 9 * ((m + 1) ^ 3 * (E + 1)) := by ring
  have h7 := one_le_powX m E 3
  omega


include hc hwf hsz hb in
theorem cost_prodRules :
    (prodRulesC (normalizeTrace ceq g s).uterm (normalizeTrace ceq g s).ubin).2 ≤
      12 * ((m + 1) ^ 3 * (E + 1)) := by
  obtain ⟨_, ht2⟩ := trace_uterm_facts s hc hwf hsz hb
  obtain ⟨_, hb2⟩ := trace_ubin_facts s hc hwf hsz hb
  show (mapC _ _).2 + (mapC _ _).2 + (appendC _ _).2 ≤ _
  rw [mapC_snd, mapC_snd, appendC_snd, mapC_fst, List.length_map]
  have h1 : m * m * m ≤ (m + 1) ^ 3 * (E + 1) := by
    calc m * m * m ≤ (m + 1) ^ 3 := by nlinarith
      _ ≤ (m + 1) ^ 3 * (E + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 := one_le_powX m E 3
  omega

include hc hwf hsz hb in
theorem cost_prod :
    (hornC ceq g.states (prodRulesC (normalizeTrace ceq g s).uterm
      (normalizeTrace ceq g s).ubin).1).2 ≤ 32 * ((m + 1) ^ 5 * (E + 1)) := by
  obtain ⟨ht1, ht2⟩ := trace_uterm_facts s hc hwf hsz hb
  obtain ⟨hb1, hb2⟩ := trace_ubin_facts s hc hwf hsz hb
  rw [prodRulesC_fst]
  have hat := prodRules_atoms g.states _ _ ht1 hb1
  have h1 := hornC_cost_le hb g.states _ (fun y h => h) (fun r hr => (hat r hr).1)
    (fun r hr => (hat r hr).2)
  have hRM : ruleMeasure (prodRules (normalizeTrace ceq g s).uterm
      (normalizeTrace ceq g s).ubin) ≤ 4 * (m + 1) ^ 3 := by
    unfold ruleMeasure
    rw [prodRules_length, prodRules_bodySize]
    have : m * m * m + 1 ≤ (m + 1) ^ 3 := by nlinarith
    omega
  have hst := hsz.states
  refine le_trans h1 ?_
  calc _ ≤ 8 * (m + 1) ^ 2 * (4 * (m + 1) ^ 3) * (E + 1) := by gcongr <;> omega
    _ = 32 * ((m + 1) ^ 5 * (E + 1)) := by ring

include hc hwf hsz hb in
theorem cost_prodBin :
    (prodBinC ceq (normalizeTrace ceq g s).prod (normalizeTrace ceq g s).ubin).2 ≤
      9 * ((m + 1) ^ 4 * (E + 1)) := by
  obtain ⟨hp1, hp2⟩ := trace_prod_facts s hc hwf hsz hb
  obtain ⟨hb1, hb2⟩ := trace_ubin_facts s hc hwf hsz hb
  unfold prodBinC
  refine le_trans (filterC_snd_le _ (3 * (m * (E + 1) + 1) + 1) _ ?_) ?_
  · intro t ht
    have := hb1 t ht
    have h1 := memC_le_states hb t.1 this.1 _ hp1 hp2
    have h2 := memC_le_states hb t.2.1 this.2.1 _ hp1 hp2
    have h3 := memC_le_states hb t.2.2 this.2.2 _ hp1 hp2
    show _ + _ + _ + 1 ≤ _
    omega
  have hi : 3 * (m * (E + 1) + 1) + 1 + 1 ≤ 8 * ((m + 1) * (E + 1)) := by nlinarith
  have h4 : (normalizeTrace ceq g s).ubin.length * (3 * (m * (E + 1) + 1) + 1 + 1) ≤
      8 * ((m + 1) ^ 4 * (E + 1)) := by
    calc _ ≤ (m + 1) ^ 3 * (8 * ((m + 1) * (E + 1))) := by
          apply Nat.mul_le_mul _ hi
          have : m * m * m ≤ (m + 1) ^ 3 := by nlinarith
          omega
      _ = 8 * ((m + 1) ^ 4 * (E + 1)) := by ring
  have h5 := one_le_powX m E 4
  omega

include hc hwf hsz hb in
theorem cost_reachRules :
    (reachRulesC s (normalizeTrace ceq g s).pbin).2 ≤ 13 * ((m + 1) ^ 3 * (E + 1)) := by
  obtain ⟨_, hp2⟩ := trace_pbin_facts s hc hwf hsz hb
  show (forListC _ _).2 + 1 ≤ _
  obtain ⟨_, h⟩ := forListC_bound_const (fun t : S × S × S =>
    ([(t.2.1, [t.1]), (t.2.2, [t.1])], 5)) 5 (normalizeTrace ceq g s).pbin
    (fun _ _ => ⟨by simp, le_refl _⟩)
  have h1 : m * m * m ≤ (m + 1) ^ 3 * (E + 1) := by
    calc m * m * m ≤ (m + 1) ^ 3 := by nlinarith
      _ ≤ (m + 1) ^ 3 * (E + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have h2 := one_le_powX m E 3
  omega

include hc hwf hsz hb hs in
theorem cost_reach :
    (hornC ceq g.states (reachRulesC s (normalizeTrace ceq g s).pbin).1).2 ≤
      32 * ((m + 1) ^ 5 * (E + 1)) := by
  obtain ⟨hp1, hp2⟩ := trace_pbin_facts s hc hwf hsz hb
  rw [reachRulesC_fst hc]
  have hat := reachRules_atoms g.states s _ hs hp1
  have h1 := hornC_cost_le hb g.states _ (fun y h => h) (fun r hr => (hat r hr).1)
    (fun r hr => (hat r hr).2)
  have hRM : ruleMeasure (reachRules s (normalizeTrace ceq g s).pbin) ≤ 4 * (m + 1) ^ 3 := by
    unfold ruleMeasure
    rw [reachRules_length, reachRules_bodySize]
    have : 4 * (m * m * m) + 2 ≤ 4 * (m + 1) ^ 3 := by nlinarith
    omega
  have hst := hsz.states
  refine le_trans h1 ?_
  calc _ ≤ 8 * (m + 1) ^ 2 * (4 * (m + 1) ^ 3) * (E + 1) := by gcongr <;> omega
    _ = 32 * ((m + 1) ^ 5 * (E + 1)) := by ring

include hc hwf hsz hb hs in
theorem cost_outTerm :
    (outTermC ceq (normalizeTrace ceq g s).reach (normalizeTrace ceq g s).uterm).2 ≤
      5 * ((m + 1) ^ 4 * (E + 1)) := by
  obtain ⟨hr1, hr2⟩ := trace_reach_facts s hc hwf hsz hb hs
  obtain ⟨ht1, ht2⟩ := trace_uterm_facts s hc hwf hsz hb
  unfold outTermC
  refine le_trans (filterC_snd_le _ (m * (E + 1) + 1 + 1) _ ?_) ?_
  · intro p hp
    have h1 := memC_le_states hb p.1 (ht1 p hp) _ hr1 hr2
    show _ + 1 ≤ _
    omega
  have hi : m * (E + 1) + 1 + 1 + 1 ≤ 4 * ((m + 1) * (E + 1)) := by nlinarith
  have h4 : (normalizeTrace ceq g s).uterm.length * (m * (E + 1) + 1 + 1 + 1) ≤
      4 * ((m + 1) ^ 4 * (E + 1)) := by
    calc _ ≤ (m + 1) ^ 3 * (4 * ((m + 1) * (E + 1))) := by
          apply Nat.mul_le_mul _ hi
          have : m * m * m ≤ (m + 1) ^ 3 := by nlinarith
          omega
      _ = 4 * ((m + 1) ^ 4 * (E + 1)) := by ring
  have h5 := one_le_powX m E 4
  omega

include hc hwf hsz hb hs in
theorem cost_outBin :
    (outBinC ceq (normalizeTrace ceq g s).reach (normalizeTrace ceq g s).pbin).2 ≤
      5 * ((m + 1) ^ 4 * (E + 1)) := by
  obtain ⟨hr1, hr2⟩ := trace_reach_facts s hc hwf hsz hb hs
  obtain ⟨hp1, hp2⟩ := trace_pbin_facts s hc hwf hsz hb
  unfold outBinC
  refine le_trans (filterC_snd_le _ (m * (E + 1) + 1 + 1) _ ?_) ?_
  · intro t ht
    have h1 := memC_le_states hb t.1 (hp1 t ht).1 _ hr1 hr2
    show _ + 1 ≤ _
    omega
  have hi : m * (E + 1) + 1 + 1 + 1 ≤ 4 * ((m + 1) * (E + 1)) := by nlinarith
  have h4 : (normalizeTrace ceq g s).pbin.length * (m * (E + 1) + 1 + 1 + 1) ≤
      4 * ((m + 1) ^ 4 * (E + 1)) := by
    calc _ ≤ (m + 1) ^ 3 * (4 * ((m + 1) * (E + 1))) := by
          apply Nat.mul_le_mul _ hi
          have : m * m * m ≤ (m + 1) ^ 3 := by nlinarith
          omega
      _ = 4 * ((m + 1) ^ 4 * (E + 1)) := by ring
  have h5 := one_le_powX m E 4
  omega

include hc hwf hsz hb hs in
theorem cost_flags :
    (memC ceq s (normalizeTrace ceq g s).prod).2 + (memC ceq s (normalizeTrace ceq g s).null).2
      ≤ 4 * ((m + 1) * (E + 1)) := by
  obtain ⟨hp1, hp2⟩ := trace_prod_facts s hc hwf hsz hb
  obtain ⟨hn1, hn2⟩ := trace_null_facts s hc hwf hsz hb
  have h1 := memC_le_states hb s hs _ hp1 hp2
  have h2 := memC_le_states hb s hs _ hn1 hn2
  have : m * (E + 1) + 1 ≤ 2 * ((m + 1) * (E + 1)) := by nlinarith
  omega

include hc hwf hsz hb hs in
/-- **Operation count of the normalizer**: `≤ 400 · (m + 1)^5 · (E + 1)` steps, where
`m` bounds every list of the front-end code and `E` bounds one state comparison. -/
theorem normalizeTrace_steps_le :
    (normalizeTrace ceq g s).steps ≤ 400 * ((m + 1) ^ 5 * (E + 1)) := by
  rw [trace_steps]
  have k1 := cost_null hwf hsz hb (ceq := ceq)
  have k2 := cost_eps s hc hwf hsz hb
  have k3 := cost_unitClosure s hc hwf hsz hb
  have k4 := cost_unitFreeTerm s hc hwf hsz hb
  have k5 := cost_unitFreeBin s hc hwf hsz hb
  have k6 := cost_prodRules s hc hwf hsz hb
  have k7 := cost_prod s hc hwf hsz hb
  have k8 := cost_prodBin s hc hwf hsz hb
  have k9 := cost_reachRules s hc hwf hsz hb
  have k10 := cost_reach s hc hwf hsz hb hs
  have k11 := cost_outTerm s hc hwf hsz hb hs
  have k12 := cost_outBin s hc hwf hsz hb hs
  have k13 := cost_flags s hc hwf hsz hb hs
  have p1 := powX_mono m E 1 5 (by omega)
  have p2 := powX_mono m E 2 5 (by omega)
  have p3 := powX_mono m E 3 5 (by omega)
  have p4 := powX_mono m E 4 5 (by omega)
  have p0 := one_le_powX m E 5
  rw [pow_one] at p1
  omega

end StageCosts

end Costs

end SSBNFNorm
end TCS1
end LeanCfgProject
