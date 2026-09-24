import LeanCfgProject.TCS1.DeltaStarTyping

/-!
# TCS #1 v78: fixed-h proof kernel for Delta-star

This module develops the parser-side invariants needed for the fixed-h_star
part of the nonlinear Delta-star proposition.  The typing itself is defined
in DeltaStarTyping.lean; here we connect it to exact balance and parser
entry-height information.

The final goal of this module is the paper statement that DeltaStar.Language
is substitutable under DeltaStar.starTyping.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/-- Signed a/b balance. -/
def balance : Word Symbol → Int
  | [] => 0
  | a :: w => 1 + balance w
  | b :: w => -1 + balance w

@[simp] theorem balance_nil :
    balance ([] : Word Symbol) = 0 := by
  rfl

@[simp] theorem balance_cons_a
    (w : Word Symbol) :
    balance (a :: w) = 1 + balance w := by
  rfl

@[simp] theorem balance_cons_b
    (w : Word Symbol) :
    balance (b :: w) = -1 + balance w := by
  rfl

@[simp] theorem balance_append
    (u v : Word Symbol) :
    balance (u ++ v) = balance u + balance v := by
  induction u with
  | nil =>
      simp
  | cons s u ih =>
      cases s <;> simp [ih, add_assoc]

@[simp] theorem balance_replicate_a
    (n : Nat) :
    balance (List.replicate n a) = (n : Int) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp [ih]
      omega

@[simp] theorem balance_replicate_b
    (n : Nat) :
    balance (List.replicate n b) = -(n : Int) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [List.replicate_succ]
      simp [ih]

/-- Numerical height represented by a parser mode. -/
def modeHeight : Mode → Int
  | .zero => 0
  | .rising n => (n : Int) + 1
  | .falling n => (n : Int) + 1

theorem modeHeight_nonneg
    (q : Mode) :
    0 ≤ modeHeight q := by
  cases q <;> simp [modeHeight] <;> omega

/-- One successful parser step changes height by the symbol balance. -/
theorem step_height
    {q r : Mode} {s : Symbol}
    (hstep : step q s = some r) :
    modeHeight r =
      modeHeight q + balance [s] := by
  cases q with
  | zero =>
      cases s with
      | a =>
          simp [step] at hstep
          subst r
          simp [modeHeight]
      | b =>
          simp [step] at hstep
  | rising n =>
      cases s with
      | a =>
          simp [step] at hstep
          subst r
          simp [modeHeight]
      | b =>
          cases n with
          | zero =>
              simp [step] at hstep
              subst r
              simp [modeHeight]
          | succ n =>
              simp [step] at hstep
              subst r
              simp [modeHeight]
  | falling n =>
      cases s with
      | a =>
          simp [step] at hstep
      | b =>
          cases n with
          | zero =>
              simp [step] at hstep
              subst r
              simp [modeHeight]
          | succ n =>
              simp [step] at hstep
              subst r
              simp [modeHeight]

/-- Peel the first successful step from a successful nonempty scan. -/
theorem scan_cons_success
    {q r : Mode} {s : Symbol}
    {w : Word Symbol}
    (hscan : scan q (s :: w) = some r) :
    ∃ q' : Mode,
      step q s = some q' ∧
      scan q' w = some r := by
  simp only [scan] at hscan
  cases hs : step q s with
  | none =>
      simp [hs] at hscan
  | some q' =>
      refine ⟨q', rfl, ?_⟩
      simpa [hs] using hscan

/-- Successful scanning realizes exact signed balance as height change. -/
theorem scan_height
    {q r : Mode} {w : Word Symbol}
    (hscan : scan q w = some r) :
    modeHeight r =
      modeHeight q + balance w := by
  induction w generalizing q with
  | nil =>
      simp [scan] at hscan
      subst r
      simp
  | cons s w ih =>
      obtain ⟨q', hstep, htail⟩ :=
        scan_cons_success hscan
      have h₁ := ih htail
      have h₂ := step_height hstep
      cases s <;> simp at h₂ ⊢ <;> omega

/-- Every accepted Delta-star word has total balance zero. -/
theorem balance_mem_zero
    {w : Word Symbol}
    (hw : w ∈ Language) :
    balance w = 0 := by
  have hh :=
    scan_height
      (q := Mode.zero)
      (r := Mode.zero)
      (w := w)
      hw
  simp [modeHeight] at hh
  omega

/-- A shared accepting context forces the two factors to have equal balance. -/
theorem balance_eq_of_sharedContext
    {x y : Word Symbol}
    (hshared : HaveSharedContext Language x y) :
    balance x = balance y := by
  rcases hshared with ⟨u, v, hx, hy⟩
  have hx0 := balance_mem_zero hx
  have hy0 := balance_mem_zero hy
  simp only [balance_append] at hx0 hy0
  omega

/--
If a b-step is immediately followed by a successful a-step, the entry height
before that b must have been exactly one.
-/
theorem step_b_then_a_entry_height_one
    {q p r : Mode}
    (hb : step q b = some p)
    (ha : step p a = some r) :
    modeHeight q = 1 := by
  cases q with
  | zero =>
      simp [step] at hb
  | rising n =>
      cases n with
      | zero =>
          simp [step] at hb
          subst p
          simp [modeHeight]
      | succ n =>
          simp [step] at hb
          subst p
          simp [step] at ha
  | falling n =>
      cases n with
      | zero =>
          simp [step] at hb
          subst p
          simp [modeHeight]
      | succ n =>
          simp [step] at hb
          subst p
          simp [step] at ha

/--
A successful scan of a factor containing an internal ba transition determines
the parser entry height uniquely.
-/
theorem entry_height_unique_of_containsBA
    {w : Word Symbol}
    {q₁ q₂ r₁ r₂ : Mode}
    (hba : containsBA w = true)
    (h₁ : scan q₁ w = some r₁)
    (h₂ : scan q₂ w = some r₂) :
    modeHeight q₁ = modeHeight q₂ := by
  induction w generalizing q₁ q₂ r₁ r₂ with
  | nil =>
      simp [containsBA] at hba
  | cons s w ih =>
      cases w with
      | nil =>
          simp [containsBA] at hba
      | cons t rest =>
          obtain ⟨p₁, hs₁, ht₁⟩ :=
            scan_cons_success h₁
          obtain ⟨p₂, hs₂, ht₂⟩ :=
            scan_cons_success h₂
          cases s with
          | a =>
              cases t with
              | a =>
                  have hba' :
                      containsBA (a :: rest) = true := by
                    simpa [containsBA] using hba
                  have hp :=
                    ih hba' ht₁ ht₂
                  have hh₁ := step_height hs₁
                  have hh₂ := step_height hs₂
                  simp at hh₁ hh₂
                  omega
              | b =>
                  have hba' :
                      containsBA (b :: rest) = true := by
                    simpa [containsBA] using hba
                  have hp :=
                    ih hba' ht₁ ht₂
                  have hh₁ := step_height hs₁
                  have hh₂ := step_height hs₂
                  simp at hh₁ hh₂
                  omega
          | b =>
              cases t with
              | a =>
                  obtain ⟨z₁, ha₁, _⟩ :=
                    scan_cons_success ht₁
                  obtain ⟨z₂, ha₂, _⟩ :=
                    scan_cons_success ht₂
                  have hq₁ :=
                    step_b_then_a_entry_height_one
                      hs₁ ha₁
                  have hq₂ :=
                    step_b_then_a_entry_height_one
                      hs₂ ha₂
                  omega
              | b =>
                  have hba' :
                      containsBA (b :: rest) = true := by
                    simpa [containsBA] using hba
                  have hp :=
                    ih hba' ht₁ ht₂
                  have hh₁ := step_height hs₁
                  have hh₂ := step_height hs₂
                  simp at hh₁ hh₂
                  omega

/-- Once a b has occurred and no ba occurs, the remaining suffix is all b's. -/
theorem suffix_all_b_of_noBA
    (w : Word Symbol)
    (hba : containsBA (b :: w) = false) :
    w = List.replicate w.length b := by
  induction w with
  | nil =>
      rfl
  | cons s w ih =>
      cases s with
      | a =>
          simp [containsBA] at hba
      | b =>
          have htail :
              containsBA (b :: w) = false := by
            simpa [containsBA] using hba
          have hw := ih htail
          rw [hw]
          simp [List.replicate_succ]

/-- A word with no internal ba factor has the canonical a* b* shape. -/
theorem noBA_shape
    (w : Word Symbol)
    (hba : containsBA w = false) :
    ∃ p q : Nat,
      w =
        List.replicate p a ++
          List.replicate q b := by
  induction w with
  | nil =>
      exact ⟨0, 0, by simp⟩
  | cons s w ih =>
      cases s with
      | a =>
          have htail :
              containsBA w = false := by
            cases w with
            | nil =>
                rfl
            | cons t rest =>
                cases t <;>
                  simpa [containsBA] using hba
          obtain ⟨p, q, hpq⟩ := ih htail
          refine ⟨p + 1, q, ?_⟩
          rw [hpq]
          simp [List.replicate_succ, List.append_assoc,
            Nat.add_comm]
      | b =>
          have hw := suffix_all_b_of_noBA w hba
          refine ⟨0, w.length + 1, ?_⟩
          rw [hw]
          simp [List.replicate_succ, Nat.add_comm]

/-- Nonempty no-ba words split into pure-a, pure-b, or mixed a+ b+ cases. -/
theorem noBA_nonempty_shape_cases
    {w : Word Symbol}
    (hne : w ≠ [])
    (hba : containsBA w = false) :
    (∃ p : Nat,
        0 < p ∧
        w = List.replicate p a) ∨
    (∃ q : Nat,
        0 < q ∧
        w = List.replicate q b) ∨
    (∃ p q : Nat,
        0 < p ∧ 0 < q ∧
        w =
          List.replicate p a ++
            List.replicate q b) := by
  obtain ⟨p, q, hpq⟩ := noBA_shape w hba
  by_cases hp0 : p = 0
  · subst p
    by_cases hq0 : q = 0
    · subst q
      simp at hpq
      exact False.elim (hne hpq)
    · right
      left
      refine ⟨q, Nat.pos_of_ne_zero hq0, ?_⟩
      simpa using hpq
  · by_cases hq0 : q = 0
    · subst q
      left
      refine ⟨p, Nat.pos_of_ne_zero hp0, ?_⟩
      simpa using hpq
    · right
      right
      exact
        ⟨p, q,
          Nat.pos_of_ne_zero hp0,
          Nat.pos_of_ne_zero hq0,
          hpq⟩


/-- Decompose an accepted word around a designated middle factor. -/
theorem scan_context_decompose
    {u x v : Word Symbol}
    (hmem : u ++ x ++ v ∈ Language) :
    ∃ q r : Mode,
      scan .zero u = some q ∧
      scan q x = some r ∧
      scan r v = some .zero := by
  change
    scan .zero (u ++ x ++ v) =
      some .zero at hmem
  rw [List.append_assoc] at hmem
  rw [scan_append] at hmem
  cases hu : scan .zero u with
  | none =>
      rw [hu] at hmem
      cases hmem
  | some q =>
      rw [hu] at hmem
      simp only at hmem
      rw [scan_append] at hmem
      cases hx : scan q x with
      | none =>
          rw [hx] at hmem
          cases hmem
      | some r =>
          rw [hx] at hmem
          simp only at hmem
          exact ⟨q, r, rfl, hx, hmem⟩

/-- Reuse a known prefix state inside another accepted context. -/
theorem scan_middle_of_context
    {u x v : Word Symbol}
    {q : Mode}
    (hu : scan .zero u = some q)
    (hmem : u ++ x ++ v ∈ Language) :
    ∃ r : Mode,
      scan q x = some r ∧
      scan r v = some .zero := by
  change
    scan .zero (u ++ x ++ v) =
      some .zero at hmem
  rw [List.append_assoc] at hmem
  rw [scan_append] at hmem
  rw [hu] at hmem
  simp only at hmem
  rw [scan_append] at hmem
  cases hx : scan q x with
  | none =>
      rw [hx] at hmem
      cases hmem
  | some r =>
      rw [hx] at hmem
      simp only at hmem
      exact ⟨r, rfl, hmem⟩

/-- Reassemble language membership from three successful scan pieces. -/
theorem mem_of_context_scans
    {u x v : Word Symbol}
    {q r : Mode}
    (hu : scan .zero u = some q)
    (hx : scan q x = some r)
    (hv : scan r v = some .zero) :
    u ++ x ++ v ∈ Language := by
  change
    scan .zero (u ++ x ++ v) =
      some .zero
  rw [List.append_assoc]
  rw [scan_append]
  rw [hu]
  simp only
  rw [scan_append]
  rw [hx]
  simp only
  exact hv

/-- A successful a-step always enters a rising mode. -/
theorem step_a_result
    {q r : Mode}
    (hstep : step q a = some r) :
    ∃ n : Nat, r = .rising n := by
  cases q with
  | zero =>
      simp [step] at hstep
      subst r
      exact ⟨0, rfl⟩
  | rising n =>
      simp [step] at hstep
      subst r
      exact ⟨n + 1, rfl⟩
  | falling n =>
      simp [step] at hstep

/-- A successful b-step ends either at zero or in a falling mode. -/
theorem step_b_result
    {q r : Mode}
    (hstep : step q b = some r) :
    r = .zero ∨
      ∃ n : Nat, r = .falling n := by
  cases q with
  | zero =>
      simp [step] at hstep
  | rising n =>
      cases n with
      | zero =>
          simp [step] at hstep
          subst r
          exact Or.inl rfl
      | succ n =>
          simp [step] at hstep
          subst r
          exact Or.inr ⟨n, rfl⟩
  | falling n =>
      cases n with
      | zero =>
          simp [step] at hstep
          subst r
          exact Or.inl rfl
      | succ n =>
          simp [step] at hstep
          subst r
          exact Or.inr ⟨n, rfl⟩

/-- Equal entry heights and the same successful symbol force equal next states. -/
theorem step_eq_of_same_height
    {q₁ q₂ p₁ p₂ : Mode}
    {s : Symbol}
    (hheight : modeHeight q₁ = modeHeight q₂)
    (h₁ : step q₁ s = some p₁)
    (h₂ : step q₂ s = some p₂) :
    p₁ = p₂ := by
  have hpheight :
      modeHeight p₁ = modeHeight p₂ := by
    have hh₁ := step_height h₁
    have hh₂ := step_height h₂
    omega
  cases s with
  | a =>
      obtain ⟨n₁, rfl⟩ := step_a_result h₁
      obtain ⟨n₂, rfl⟩ := step_a_result h₂
      simp [modeHeight] at hpheight
      have hn : n₁ = n₂ := by omega
      subst n₂
      rfl
  | b =>
      rcases step_b_result h₁ with rfl | ⟨n₁, rfl⟩ <;>
        rcases step_b_result h₂ with rfl | ⟨n₂, rfl⟩
      · rfl
      · exfalso
        simp [modeHeight] at hpheight
        omega
      · exfalso
        simp [modeHeight] at hpheight
        omega
      · simp [modeHeight] at hpheight
        have hn : n₁ = n₂ := by omega
        subst n₂
        rfl

theorem lastSymbol_eq_none_iff
    (w : Word Symbol) :
    lastSymbol? w = none ↔ w = [] := by
  cases w <;> simp [lastSymbol?]

/-- If the last processed terminal is a, a successful scan ends rising. -/
theorem scan_result_of_last_a
    {q r : Mode} {w : Word Symbol}
    (hne : w ≠ [])
    (hlast : lastSymbol? w = some a)
    (hscan : scan q w = some r) :
    ∃ n : Nat, r = .rising n := by
  induction w generalizing q with
  | nil =>
      exact False.elim (hne rfl)
  | cons s w ih =>
      cases w with
      | nil =>
          simp [lastSymbol?, lastFrom] at hlast
          subst s
          obtain ⟨q', hstep, htail⟩ :=
            scan_cons_success hscan
          have hqr : q' = r := by
            simpa [scan] using htail
          subst r
          exact step_a_result hstep
      | cons t rest =>
          obtain ⟨q', hstep, htail⟩ :=
            scan_cons_success hscan
          have hlast' :
              lastSymbol? (t :: rest) = some a := by
            simpa [lastSymbol?, lastFrom] using hlast
          exact
            ih (q := q')
              (by simp) hlast' htail

/-- If the last processed terminal is b, a successful scan ends zero or falling. -/
theorem scan_result_of_last_b
    {q r : Mode} {w : Word Symbol}
    (hne : w ≠ [])
    (hlast : lastSymbol? w = some b)
    (hscan : scan q w = some r) :
    r = .zero ∨
      ∃ n : Nat, r = .falling n := by
  induction w generalizing q with
  | nil =>
      exact False.elim (hne rfl)
  | cons s w ih =>
      cases w with
      | nil =>
          simp [lastSymbol?, lastFrom] at hlast
          subst s
          obtain ⟨q', hstep, htail⟩ :=
            scan_cons_success hscan
          have hqr : q' = r := by
            simpa [scan] using htail
          subst r
          exact step_b_result hstep
      | cons t rest =>
          obtain ⟨q', hstep, htail⟩ :=
            scan_cons_success hscan
          have hlast' :
              lastSymbol? (t :: rest) = some b := by
            simpa [lastSymbol?, lastFrom] using hlast
          exact
            ih (q := q')
              (by simp) hlast' htail

/--
With the same entry mode, equal balance and equal last symbol force equal
successful exit modes.
-/
theorem scan_final_eq_of_balance_last
    {q r₁ r₂ : Mode}
    {x y : Word Symbol}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hbal : balance x = balance y)
    (hlast : lastSymbol? x = lastSymbol? y)
    (hx : scan q x = some r₁)
    (hy : scan q y = some r₂) :
    r₁ = r₂ := by
  have hh₁ := scan_height hx
  have hh₂ := scan_height hy
  have hh :
      modeHeight r₁ = modeHeight r₂ := by
    omega
  cases hxl : lastSymbol? x with
  | none =>
      exact
        False.elim
          (hxne ((lastSymbol_eq_none_iff x).1 hxl))
  | some s =>
      have hyl :
          lastSymbol? y = some s := by
        rw [← hlast]
        exact hxl
      cases s with
      | a =>
          obtain ⟨n₁, rfl⟩ :=
            scan_result_of_last_a hxne hxl hx
          obtain ⟨n₂, rfl⟩ :=
            scan_result_of_last_a hyne hyl hy
          simp [modeHeight] at hh
          have hn : n₁ = n₂ := by omega
          subst n₂
          rfl
      | b =>
          rcases
              scan_result_of_last_b hxne hxl hx with
              rfl | ⟨n₁, rfl⟩ <;>
            rcases
              scan_result_of_last_b hyne hyl hy with
              rfl | ⟨n₂, rfl⟩
          · rfl
          · exfalso
            simp [modeHeight] at hh
            omega
          · exfalso
            simp [modeHeight] at hh
            omega
          · simp [modeHeight] at hh
            have hn : n₁ = n₂ := by omega
            subst n₂
            rfl

@[simp] theorem lastFrom_replicate_same
    (s : Symbol) (n : Nat) :
    lastFrom s (List.replicate n s) = s := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [List.replicate_succ]
      simp [lastFrom, ih]

theorem lastFrom_append_single
    (s : Symbol)
    (w : Word Symbol)
    (t : Symbol) :
    lastFrom s (w ++ [t]) = t := by
  induction w generalizing s with
  | nil =>
      rfl
  | cons z w ih =>
      simp [lastFrom, ih]

theorem lastSymbol_append_single
    (w : Word Symbol)
    (s : Symbol) :
    lastSymbol? (w ++ [s]) = some s := by
  cases w with
  | nil =>
      rfl
  | cons t w =>
      simp [lastSymbol?, lastFrom_append_single]

theorem firstSymbol_replicate_pos
    (s : Symbol)
    {n : Nat}
    (hn : 0 < n) :
    firstSymbol? (List.replicate n s) =
      some s := by
  cases n with
  | zero =>
      omega
  | succ n =>
      simp [List.replicate_succ, firstSymbol?]

theorem lastSymbol_replicate_pos
    (s : Symbol)
    {n : Nat}
    (hn : 0 < n) :
    lastSymbol? (List.replicate n s) =
      some s := by
  cases n with
  | zero =>
      omega
  | succ n =>
      rw [← replicate_succ_right s n]
      exact lastSymbol_append_single
        (List.replicate n s) s

theorem firstSymbol_mixed
    {p q : Nat}
    (hp : 0 < p) :
    firstSymbol?
        (List.replicate p a ++
          List.replicate q b) =
      some a := by
  cases p with
  | zero =>
      omega
  | succ p =>
      simp [List.replicate_succ, firstSymbol?]

theorem lastSymbol_mixed
    {p q : Nat}
    (hq : 0 < q) :
    lastSymbol?
        (List.replicate p a ++
          List.replicate q b) =
      some b := by
  cases q with
  | zero =>
      omega
  | succ q =>
      rw [← replicate_succ_right b q]
      simpa [List.append_assoc] using
        lastSymbol_append_single
          (List.replicate p a ++
            List.replicate q b) b

/-- A falling state can read any b-prefix no longer than its current height. -/
theorem exists_scan_falling_replicate_b_of_le
    (h q : Nat)
    (hle : q ≤ h + 1) :
    ∃ r : Mode,
      scan (.falling h)
          (List.replicate q b) =
        some r := by
  induction q generalizing h with
  | zero =>
      exact ⟨.falling h, rfl⟩
  | succ q ih =>
      cases h with
      | zero =>
          have hq : q = 0 := by omega
          subst q
          exact ⟨.zero, by simp [List.replicate_succ, scan, step]⟩
      | succ h =>
          have hle' : q ≤ h + 1 := by omega
          obtain ⟨r, hr⟩ := ih (h := h) hle'
          refine ⟨r, ?_⟩
          rw [List.replicate_succ]
          simp only [scan, step]
          exact hr

/-- A rising state can read any b-prefix no longer than its current height. -/
theorem exists_scan_rising_replicate_b_of_le
    (h q : Nat)
    (hle : q ≤ h + 1) :
    ∃ r : Mode,
      scan (.rising h)
          (List.replicate q b) =
        some r := by
  cases q with
  | zero =>
      exact ⟨.rising h, rfl⟩
  | succ q =>
      cases h with
      | zero =>
          have hq : q = 0 := by omega
          subst q
          exact ⟨.zero, by simp [List.replicate_succ, scan, step]⟩
      | succ h =>
          have hle' : q ≤ h + 1 := by omega
          obtain ⟨r, hr⟩ :=
            exists_scan_falling_replicate_b_of_le
              h q hle'
          refine ⟨r, ?_⟩
          rw [List.replicate_succ]
          simp only [scan, step]
          exact hr

theorem scan_zero_replicate_a_succ
    (p : Nat) :
    scan .zero
        (List.replicate (p + 1) a) =
      some (.rising p) := by
  rw [List.replicate_succ]
  simp only [scan, step]
  simpa using
    scan_rising_replicate_a 0 p

/--
For a mixed a+ b+ word, successful scanning depends on the entry mode and on
the signed exponent difference, not on the individual exponents.
-/
theorem scan_mixed_exists_of_same_balance
    {entry r : Mode}
    {p q p' q' : Nat}
    (hp : 0 < p)
    (hq : 0 < q)
    (hp' : 0 < p')
    (hq' : 0 < q')
    (hbal :
      (p : Int) - (q : Int) =
        (p' : Int) - (q' : Int))
    (hscan :
      scan entry
          (List.replicate p a ++
            List.replicate q b) =
        some r) :
    ∃ r' : Mode,
      scan entry
          (List.replicate p' a ++
            List.replicate q' b) =
        some r' := by
  cases entry with
  | falling n =>
      cases p with
      | zero =>
          omega
      | succ p =>
          rw [List.replicate_succ] at hscan
          simp [scan, step] at hscan
  | zero =>
      cases p with
      | zero =>
          omega
      | succ p =>
          cases p' with
          | zero =>
              omega
          | succ p' =>
              rw [scan_append,
                scan_zero_replicate_a_succ] at hscan
              have hh := scan_height hscan
              have hrnonneg := modeHeight_nonneg r
              have hle : q ≤ p + 1 := by
                rw [balance_replicate_b] at hh
                change
                  modeHeight r =
                    ((p : Int) + 1) + -(q : Int) at hh
                omega
              have hle' : q' ≤ p' + 1 := by
                omega
              obtain ⟨r', hr'⟩ :=
                exists_scan_rising_replicate_b_of_le
                  p' q' hle'
              refine ⟨r', ?_⟩
              rw [scan_append,
                scan_zero_replicate_a_succ]
              exact hr'
  | rising n =>
      rw [scan_append,
        scan_rising_replicate_a] at hscan
      have hh := scan_height hscan
      have hrnonneg := modeHeight_nonneg r
      have hle : q ≤ n + p + 1 := by
        rw [balance_replicate_b] at hh
        change
          modeHeight r =
            (((n + p : Nat) : Int) + 1) + -(q : Int) at hh
        omega
      have hle' : q' ≤ n + p' + 1 := by
        omega
      obtain ⟨r', hr'⟩ :=
        exists_scan_rising_replicate_b_of_le
          (n + p') q' (by omega)
      refine ⟨r', ?_⟩
      rw [scan_append,
        scan_rising_replicate_a]
      exact hr'

end DeltaStar
end TCS1
end LeanCfgProject
