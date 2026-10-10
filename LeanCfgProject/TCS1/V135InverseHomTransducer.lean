import Mathlib.Tactic.Ring

/-!
# TCS #1 v135: the letter-position transducer for inverse homomorphisms

Fix letter images `φ : Γ → List Σ` (a possibly erasing homomorphism
`Γ* → Σ*`).  The CFL side of `prop:finite-info-closure` (iii) is proved by
running a CFG for `L ⊆ Σ*` through the following finite-state device, which
reads `φ(y)` and outputs `y`:

* state `none`: at a letter boundary;
* state `some (c, r)`: inside the image of the letter `c`, still expecting the
  nonempty suffix `r` of `φ(c)`.

Reading `a` at a boundary *starts* a letter `c` with `φ(c) = a :: r` and
outputs `c`; reading `a` inside `c` with remaining `a :: r` outputs nothing.
Erasing letters are never output here; they are inserted by a separate step
(`InsertZ`, below).

Main facts:
* `run_none_none_iff`: `Run none u none y ↔ y.flatMap φ = u ∧ ∀ c ∈ y, φ c ≠ []`;
* `run_append_split` / `run_append`: runs split and concatenate along `u`;
* `insertZ_iff`: the insertion relation captures exactly "delete the letters
  of `Z` from `y`".
-/

namespace LeanCfgProject
namespace TCS1
namespace InverseHom

set_option linter.unusedSectionVars false

universe u v

section Transducer

variable {Γ : Type u} {Sig : Type v} (φ : Γ → List Sig)

/-- Transducer states. -/
abbrev TState (Γ : Type u) (Sig : Type v) := Option (Γ × List Sig)

/-- Normalize a remaining suffix: an exhausted letter returns to the boundary. -/
def tnorm (c : Γ) : List Sig → TState Γ Sig
  | [] => none
  | a :: r => some (c, a :: r)

/-- The remaining input expected by a state. -/
def trem : TState Γ Sig → List Sig
  | none => []
  | some (_, r) => r

theorem trem_tnorm (c : Γ) (r : List Sig) : trem (tnorm c r) = r := by
  cases r <;> rfl

/-- One transition, reading one input letter and emitting a (0- or
1-letter) output word. -/
inductive TStep : TState Γ Sig → Sig → TState Γ Sig → List Γ → Prop
  | start {c : Γ} {a : Sig} {r : List Sig} (h : φ c = a :: r) :
      TStep none a (tnorm c r) [c]
  | inside {c : Γ} {a : Sig} {r : List Sig} :
      TStep (some (c, a :: r)) a (tnorm c r) []

/-- Runs of the transducer: input `u`, output `y`. -/
inductive TRun : TState Γ Sig → List Sig → TState Γ Sig → List Γ → Prop
  | nil (s : TState Γ Sig) : TRun s [] s []
  | cons {s q t : TState Γ Sig} {a : Sig} {u : List Sig} {o y : List Γ}
      (hs : TStep φ s a q o) (hr : TRun q u t y) : TRun s (a :: u) t (o ++ y)

/-- Soundness invariant of a run. -/
theorem trun_sound {s t : TState Γ Sig} {u : List Sig} {y : List Γ}
    (h : TRun φ s u t y) :
    u ++ trem t = trem s ++ y.flatMap φ ∧ ∀ c, c ∈ y → φ c ≠ [] := by
  induction h with
  | nil s => simp
  | @cons s q t a u o y hs hr ih =>
      obtain ⟨ih1, ih2⟩ := ih
      cases hs with
      | @start c a r hc =>
          refine ⟨?_, ?_⟩
          · rw [trem_tnorm] at ih1
            show a :: (u ++ trem t) = ([c] ++ y).flatMap φ
            rw [ih1]
            simp [hc]
          · intro c' hc'
            rcases List.mem_cons.mp hc' with rfl | hc'
            · rw [hc]; simp
            · exact ih2 c' hc'
      | @inside c a r =>
          refine ⟨?_, ?_⟩
          · rw [trem_tnorm] at ih1
            show a :: (u ++ trem t) = (a :: r) ++ y.flatMap φ
            rw [ih1]
            rfl
          · intro c' hc'
            exact ih2 c' (by simpa using hc')

/-- Consuming the remaining part of a started letter. -/
theorem trun_consume (c : Γ) :
    ∀ (r : List Sig) {u : List Sig} {t : TState Γ Sig} {y : List Γ},
      TRun φ none u t y → TRun φ (tnorm c r) (r ++ u) t y
  | [], _, _, _, h => h
  | a :: r, u, t, y, h => by
      have h' := TRun.cons (TStep.inside (φ := φ) (c := c) (a := a) (r := r))
        (trun_consume c r h)
      show TRun φ (some (c, a :: r)) (a :: (r ++ u)) t y
      simpa using h'

/-- Completeness at the boundary: every word of nonerasing letters is output
on its own image. -/
theorem trun_complete : ∀ y : List Γ, (∀ c, c ∈ y → φ c ≠ []) →
    TRun φ none (y.flatMap φ) none y
  | [], _ => TRun.nil none
  | c :: y, hy => by
      have hc := hy c (by simp)
      have ih := trun_complete y (fun c' hc' => hy c' (by simp [hc']))
      obtain ⟨a, r, har⟩ : ∃ a r, φ c = a :: r := by
        cases h : φ c with
        | nil => exact absurd h hc
        | cons a r => exact ⟨a, r, rfl⟩
      have h1 := TRun.cons (TStep.start (φ := φ) har) (trun_consume φ c r ih)
      have e : (c :: y).flatMap φ = a :: (r ++ y.flatMap φ) := by
        simp [har]
      rw [e]
      simpa using h1

/-- **Boundary-to-boundary runs are exactly the inverse image under `φ`
restricted to nonerasing letters.** -/
theorem trun_none_none_iff (u : List Sig) (y : List Γ) :
    TRun φ none u none y ↔ y.flatMap φ = u ∧ ∀ c, c ∈ y → φ c ≠ [] := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := trun_sound φ h
    simp only [trem, List.append_nil, List.nil_append] at h1
    exact ⟨h1.symm, h2⟩
  · rintro ⟨rfl, h⟩
    exact trun_complete φ y h

/-- Runs split along a concatenation of the input. -/
theorem trun_append_split : ∀ {s t : TState Γ Sig} {u₁ u₂ : List Sig} {y : List Γ},
    TRun φ s (u₁ ++ u₂) t y →
      ∃ q y₁ y₂, y = y₁ ++ y₂ ∧ TRun φ s u₁ q y₁ ∧ TRun φ q u₂ t y₂ := by
  intro s t u₁
  induction u₁ generalizing s with
  | nil =>
      intro u₂ y h
      exact ⟨s, [], y, rfl, TRun.nil s, h⟩
  | cons a u₁ ih =>
      intro u₂ y h
      cases h with
      | @cons _ q _ _ _ o y' hs hr =>
          obtain ⟨q', y₁, y₂, rfl, h1, h2⟩ := ih hr
          exact ⟨q', o ++ y₁, y₂, by simp, TRun.cons hs h1, h2⟩

/-- Runs concatenate. -/
theorem trun_append {s q t : TState Γ Sig} {u₁ u₂ : List Sig} {y₁ y₂ : List Γ}
    (h₁ : TRun φ s u₁ q y₁) (h₂ : TRun φ q u₂ t y₂) :
    TRun φ s (u₁ ++ u₂) t (y₁ ++ y₂) := by
  induction h₁ with
  | nil s => simpa using h₂
  | @cons s q' t' a u o y hs hr ih =>
      have := TRun.cons hs (ih h₂)
      simpa [List.append_assoc] using this

/-- Valid states: the boundary, or a nonempty suffix of some image. -/
def TValid : TState Γ Sig → Prop
  | none => True
  | some (c, r) => r ≠ [] ∧ r <:+ φ c

theorem tvalid_tnorm {c : Γ} {r : List Sig} (h : r <:+ φ c) :
    TValid φ (tnorm c r) := by
  cases r with
  | nil => trivial
  | cons a r => exact ⟨by simp, h⟩

theorem tstep_valid {s q : TState Γ Sig} {a : Sig} {o : List Γ}
    (h : TStep φ s a q o) (hs : TValid φ s) : TValid φ q := by
  cases h with
  | @start c a r hc =>
      apply tvalid_tnorm
      rw [hc]
      exact List.suffix_cons a r
  | @inside c a r =>
      apply tvalid_tnorm
      obtain ⟨_, ht⟩ := hs
      exact (List.suffix_cons a r).trans ht

theorem trun_valid {s t : TState Γ Sig} {u : List Sig} {y : List Γ}
    (h : TRun φ s u t y) (hs : TValid φ s) : TValid φ t := by
  induction h with
  | nil s => exact hs
  | cons hstep _ ih => exact ih (tstep_valid φ hstep hs)

end Transducer

section Insertion

variable {Γ : Type u} (Z : Γ → Prop)

/-- `InsertZ y₁ y`: `y` is obtained from `y₁` by inserting `Z`-letters
*before* each letter of `y₁` (none after the last letter). -/
inductive InsertZ : List Γ → List Γ → Prop
  | nil : InsertZ [] []
  | cons {c : Γ} {y₁ y e : List Γ} (he : ∀ d, d ∈ e → Z d) (h : InsertZ y₁ y) :
      InsertZ (c :: y₁) (e ++ c :: y)

/-- Inserting before every letter, plus a trailing block, captures exactly the
words whose `Z`-free part is `y₁`, when `y₁` itself has no `Z`-letters. -/
theorem insertZ_trailing_iff [DecidablePred Z] (y₁ y : List Γ)
    (h₁ : ∀ c, c ∈ y₁ → ¬ Z c) :
    (∃ y' e, y = y' ++ e ∧ InsertZ Z y₁ y' ∧ ∀ d, d ∈ e → Z d) ↔
      y.filter (fun c => !decide (Z c)) = y₁ := by
  constructor
  · rintro ⟨y', e, rfl, hins, he⟩
    have hfe : e.filter (fun c => !decide (Z c)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro d hd
      simp [he d hd]
    rw [List.filter_append, hfe, List.append_nil]
    clear hfe he
    induction hins with
    | nil => rfl
    | @cons c y₁ y e he h ih =>
        have hc : ¬ Z c := h₁ c (by simp)
        have hfe : e.filter (fun c => !decide (Z c)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro d hd
          simp [he d hd]
        rw [List.filter_append, hfe, List.nil_append, List.filter_cons_of_pos (by simp [hc]),
          ih (fun c' hc' => h₁ c' (by simp [hc']))]
  · intro hfil
    subst hfil
    clear h₁
    induction y with
    | nil => exact ⟨[], [], rfl, InsertZ.nil, by simp⟩
    | cons c y ih =>
        obtain ⟨y', e, rfl, hins, he⟩ := ih
        by_cases hc : Z c
        · rw [List.filter_cons_of_neg (by simp [hc])]
          -- prepend `c` to the first inserted block (or to the trailing block)
          generalize hF : (y' ++ e).filter (fun c => !decide (Z c)) = F at hins ⊢
          cases hins with
          | nil =>
              exact ⟨[], c :: e, by simp, InsertZ.nil, by
                intro d hd
                rcases List.mem_cons.mp hd with rfl | hd
                · exact hc
                · exact he d hd⟩
          | @cons c' y₁ y'' e' he' h =>
              refine ⟨(c :: e') ++ c' :: y'', e, by simp, InsertZ.cons ?_ h, he⟩
              intro d hd
              rcases List.mem_cons.mp hd with rfl | hd
              · exact hc
              · exact he' d hd
        · rw [List.filter_cons_of_pos (by simp [hc])]
          exact ⟨[] ++ c :: y', e, by simp, InsertZ.cons (by simp) hins, he⟩

end Insertion

end InverseHom
end TCS1
end LeanCfgProject
