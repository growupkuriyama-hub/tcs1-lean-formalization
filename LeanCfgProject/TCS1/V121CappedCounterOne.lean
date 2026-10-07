import LeanCfgProject.TCS1.CappedCounterFixedWindow

/-!
# TCS #1 v121: sharp rho = 1 capped-counter boundary

The v121 manuscript sharpens the capped-counter example by observing that the
rho >= 2 lower bound is exact: CTR_1 is (1,1)-substitutable.

This file proves that statement directly from the scanner semantics.  The key
rho=1 fact is that, whenever a one-letter word can be read from two live
heights, its resulting live height is the same.  Hence two successful factors
with the same first and last one-letter windows can be transported between
contexts.
-/

namespace LeanCfgProject
namespace TCS1
namespace CappedCounter

/-- A successful scan of a concatenation factors through a live intermediate
height. -/
theorem scan_success_split
    {rho h t : Nat}
    {u v : Word Symbol}
    (hs : scan rho h (u ++ v) = some t) :
    ∃ m : Nat,
      scan rho h u = some m ∧
      scan rho m v = some t := by
  rw [scan_append] at hs
  cases hm : scan rho h u with
  | none =>
      simp [hm] at hs
  | some m =>
      exact ⟨m, rfl, by simpa using hs⟩

/-- Successful scans compose. -/
theorem scan_success_join
    {rho h m t : Nat}
    {u v : Word Symbol}
    (hu : scan rho h u = some m)
    (hv : scan rho m v = some t) :
    scan rho h (u ++ v) = some t := by
  rw [scan_append, hu]
  exact hv

/-- Starting inside the cap, every successful result is still inside the cap. -/
theorem scan_result_le_cap
    {rho h t : Nat}
    {w : Word Symbol}
    (hh : h ≤ rho)
    (hs : scan rho h w = some t) :
    t ≤ rho := by
  induction w generalizing h with
  | nil =>
      simp [scan] at hs
      subst t
      exact hh
  | cons s w ih =>
      cases s with
      | up =>
          by_cases hlt : h < rho
          · simp only [scan, if_pos hlt] at hs
            exact ih (by omega) hs
          · simp [scan, hlt] at hs
      | down =>
          cases h with
          | zero =>
              simp [scan] at hs
          | succ h =>
              simp only [scan] at hs
              exact ih (by omega) hs
      | reset =>
          simp only [scan] at hs
          exact ih (Nat.zero_le rho) hs

/--
At cap one, a readable single letter has an output height determined by the
letter alone, independently of which live input height made the read possible.
-/
theorem scan_one_singleton_output_unique
    {a b r s : Nat}
    {p : Word Symbol}
    (ha : a ≤ 1)
    (hb : b ≤ 1)
    (hp : p.length = 1)
    (har : scan 1 a p = some r)
    (hbs : scan 1 b p = some s) :
    r = s := by
  cases p with
  | nil =>
      simp at hp
  | cons z rest =>
      cases rest with
      | nil =>
          have ha01 : a = 0 ∨ a = 1 := by omega
          have hb01 : b = 0 ∨ b = 1 := by omega
          rcases ha01 with rfl | rfl <;>
            rcases hb01 with rfl | rfl <;>
            cases z <;>
            simp [scan] at har hbs <;>
            omega
      | cons z' rest =>
          simp at hp

/-- The v121 sharpness statement: CTR_1 belongs to the (1,1)-substitutable
class. -/
theorem fixedWindowSubstitutable_one :
    FixedWindowSubstitutable 1 1 (Language 1) := by
  intro p q y₁ y₂ x₁ x₂ z₁ z₂
    hp hq hf₁ne hf₂ne h₁ h₂ h₃

  rcases h₁ with ⟨t₁, hs₁⟩
  rcases h₂ with ⟨t₂, hs₂⟩
  rcases h₃ with ⟨t₃, hs₃⟩

  let f₁ : Word Symbol := p ++ y₁ ++ q
  let f₂ : Word Symbol := p ++ y₂ ++ q

  have hs₁' :
      scan 1 0 (x₁ ++ f₁ ++ z₁) = some t₁ := by
    simpa [f₁, List.append_assoc] using hs₁
  have hs₂' :
      scan 1 0 (x₁ ++ f₂ ++ z₁) = some t₂ := by
    simpa [f₂, List.append_assoc] using hs₂
  have hs₃' :
      scan 1 0 (x₂ ++ f₁ ++ z₂) = some t₃ := by
    simpa [f₁, List.append_assoc] using hs₃

  have hs₁'' :
      scan 1 0 (x₁ ++ (f₁ ++ z₁)) = some t₁ := by
    simpa only [List.append_assoc] using hs₁'
  obtain ⟨a, hx₁, hf₁z₁⟩ :=
    scan_success_split (rho := 1) (h := 0)
      (u := x₁) (v := f₁ ++ z₁) hs₁''
  obtain ⟨b₁, hf₁a, hz₁⟩ :=
    scan_success_split (rho := 1) (h := a)
      (u := f₁) (v := z₁) hf₁z₁

  have hs₂'' :
      scan 1 0 (x₁ ++ (f₂ ++ z₁)) = some t₂ := by
    simpa only [List.append_assoc] using hs₂'
  have hf₂z₁ :
      scan 1 a (f₂ ++ z₁) = some t₂ := by
    rw [scan_append, hx₁] at hs₂''
    exact hs₂''
  obtain ⟨b₂, hf₂a, hz₁'⟩ :=
    scan_success_split (rho := 1) (h := a)
      (u := f₂) (v := z₁) hf₂z₁

  have hs₃'' :
      scan 1 0 (x₂ ++ (f₁ ++ z₂)) = some t₃ := by
    simpa only [List.append_assoc] using hs₃'
  obtain ⟨c, hx₂, hf₁z₂⟩ :=
    scan_success_split (rho := 1) (h := 0)
      (u := x₂) (v := f₁ ++ z₂) hs₃''
  obtain ⟨d₁, hf₁c, hz₂⟩ :=
    scan_success_split (rho := 1) (h := c)
      (u := f₁) (v := z₂) hf₁z₂

  have ha : a ≤ 1 :=
    scan_result_le_cap (rho := 1) (h := 0)
      (w := x₁) (t := a) (by omega) hx₁
  have hc : c ≤ 1 :=
    scan_result_le_cap (rho := 1) (h := 0)
      (w := x₂) (t := c) (by omega) hx₂

  obtain ⟨ap₁, hp_a₁, htail₁a⟩ :=
    scan_success_split (rho := 1) (h := a)
      (u := p) (v := y₁ ++ q)
      (by simpa [f₁, List.append_assoc] using hf₁a)
  obtain ⟨ap₂, hp_a₂, htail₂a⟩ :=
    scan_success_split (rho := 1) (h := a)
      (u := p) (v := y₂ ++ q)
      (by simpa [f₂, List.append_assoc] using hf₂a)
  obtain ⟨cp₁, hp_c₁, htail₁c⟩ :=
    scan_success_split (rho := 1) (h := c)
      (u := p) (v := y₁ ++ q)
      (by simpa [f₁, List.append_assoc] using hf₁c)

  have hap₁ : ap₁ ≤ 1 :=
    scan_result_le_cap (rho := 1) ha hp_a₁
  have hap₂ : ap₂ ≤ 1 :=
    scan_result_le_cap (rho := 1) ha hp_a₂
  have hcp₁ : cp₁ ≤ 1 :=
    scan_result_le_cap (rho := 1) hc hp_c₁

  have hp12 : ap₁ = ap₂ :=
    scan_one_singleton_output_unique
      ha ha hp hp_a₁ hp_a₂
  have hp1c : ap₁ = cp₁ :=
    scan_one_singleton_output_unique
      ha hc hp hp_a₁ hp_c₁

  have htail₂c :
      scan 1 cp₁ (y₂ ++ q) = some b₂ := by
    rw [← hp1c, hp12]
    exact htail₂a

  have hf₂c :
      scan 1 c f₂ = some b₂ := by
    have hj :=
      scan_success_join
        (rho := 1) (h := c)
        (u := p) (v := y₂ ++ q)
        hp_c₁ htail₂c
    simpa [f₂, List.append_assoc] using hj

  obtain ⟨preq₁, hpreq₁, hq₁⟩ :=
    scan_success_split (rho := 1) (h := c)
      (u := p ++ y₁) (v := q)
      (by simpa [f₁, List.append_assoc] using hf₁c)
  obtain ⟨preq₂, hpreq₂, hq₂⟩ :=
    scan_success_split (rho := 1) (h := c)
      (u := p ++ y₂) (v := q)
      (by simpa [f₂, List.append_assoc] using hf₂c)

  have hpreq₁le : preq₁ ≤ 1 :=
    scan_result_le_cap (rho := 1) hc hpreq₁
  have hpreq₂le : preq₂ ≤ 1 :=
    scan_result_le_cap (rho := 1) hc hpreq₂

  have hfinal : d₁ = b₂ :=
    scan_one_singleton_output_unique
      hpreq₁le hpreq₂le hq hq₁ hq₂

  have hf₂z₂ :
      scan 1 c (f₂ ++ z₂) = some t₃ := by
    apply scan_success_join hf₂c
    rw [← hfinal]
    exact hz₂

  have hout :
      scan 1 0 (x₂ ++ (f₂ ++ z₂)) = some t₃ :=
    scan_success_join hx₂ hf₂z₂

  refine ⟨t₃, ?_⟩
  simpa [f₂, List.append_assoc] using hout

end CappedCounter
end TCS1
end LeanCfgProject
