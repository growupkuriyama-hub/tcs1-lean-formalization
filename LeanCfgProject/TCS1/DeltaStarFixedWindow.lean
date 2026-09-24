import LeanCfgProject.TCS1.FixedWindowCounterexampleCriterion

/-!
# TCS #1 v78: Delta-star semantic kernel and fixed-window separation

The nonlinear boundary example in Section 9 is

  Delta* = ( { a^n b^n | n >= 0 } )*.

This file introduces a deterministic block parser for the same intended
language. A block starts in mode zero, rises while reading a's, then falls
while reading b's; a new a is allowed after the height has returned to zero.
The parser therefore rejects an occurrence of b a at positive height.

The main theorem verifies the manuscript's exact fixed-window witness

  s = a^N b^N,
  t = a^N b^N a^N b^N,
  N = max 1 (k+l),

with distinguishing context (a,b). The fixed-h_star and CFG/nonlinearity
parts of the proposition are handled in later layers.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

inductive Symbol where
  | a
  | b
  deriving DecidableEq, Fintype, Repr

open Symbol

inductive Mode where
  | zero
  | rising (n : Nat)
  | falling (n : Nat)
  deriving DecidableEq, Repr

def step : Mode → Symbol → Option Mode
  | .zero, a => some (.rising 0)
  | .zero, b => none
  | .rising n, a => some (.rising (n + 1))
  | .rising 0, b => some .zero
  | .rising (n + 1), b => some (.falling n)
  | .falling _, a => none
  | .falling 0, b => some .zero
  | .falling (n + 1), b => some (.falling n)

def scan : Mode → Word Symbol → Option Mode
  | q, [] => some q
  | q, s :: w =>
      match step q s with
      | none => none
      | some q' => scan q' w

theorem scan_append
    (q : Mode)
    (u v : Word Symbol) :
    scan q (u ++ v) =
      match scan q u with
      | none => none
      | some r => scan r v := by
  induction u generalizing q with
  | nil =>
      simp [scan]
  | cons s u ih =>
      simp only [List.cons_append, scan]
      cases hs : step q s with
      | none =>
          simp [hs]
      | some r =>
          simp [hs, ih]

theorem scan_rising_replicate_a
    (h n : Nat) :
    scan (.rising h)
        (List.replicate n a) =
      some (.rising (h + n)) := by
  induction n generalizing h with
  | zero =>
      simp [scan]
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [scan, step]
      have h' :=
        ih (h := h + 1)
      simpa [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using h'

theorem scan_falling_replicate_b_to_zero
    (n : Nat) :
    scan (.falling n)
        (List.replicate (n + 1) b) =
      some .zero := by
  induction n with
  | zero =>
      simp [scan, step]
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [scan, step]
      simpa using ih

theorem scan_falling_replicate_b_partial
    (n : Nat) :
    scan (.falling n)
        (List.replicate n b) =
      some (.falling 0) := by
  induction n with
  | zero =>
      simp [scan]
  | succ n ih =>
      rw [List.replicate_succ]
      simp only [scan, step]
      simpa using ih

theorem scan_rising_replicate_b_to_zero
    (n : Nat) :
    scan (.rising n)
        (List.replicate (n + 1) b) =
      some .zero := by
  cases n with
  | zero =>
      simp [scan, step]
  | succ n =>
      rw [List.replicate_succ]
      simp only [scan, step]
      exact scan_falling_replicate_b_to_zero n

theorem scan_positive_block
    (n : Nat) :
    scan .zero
        (List.replicate (n + 1) a ++
          List.replicate (n + 1) b) =
      some .zero := by
  rw [scan_append]
  rw [List.replicate_succ]
  simp only [scan, step]
  have ha :=
    scan_rising_replicate_a 0 n
  rw [ha]
  simpa using scan_rising_replicate_b_to_zero n

theorem scan_block
    (n : Nat) :
    scan .zero
        (List.replicate n a ++
          List.replicate n b) =
      some .zero := by
  cases n with
  | zero =>
      simp [scan]
  | succ n =>
      simpa using scan_positive_block n

theorem scan_rising_replicate_b_partial
    {n : Nat}
    (hn : 0 < n) :
    scan (.rising n)
        (List.replicate n b) =
      some (.falling 0) := by
  cases n with
  | zero =>
      omega
  | succ n =>
      rw [List.replicate_succ]
      simp only [scan, step]
      exact scan_falling_replicate_b_partial n

def Language : Set (Word Symbol) :=
  {w | scan .zero w = some .zero}

@[simp] theorem mem_language_iff
    (w : Word Symbol) :
    w ∈ Language ↔
      scan .zero w = some .zero := by
  rfl

theorem scan_bad_prefix
    {n : Nat}
    (hn : 0 < n) :
    scan .zero
        (List.replicate (n + 1) a ++
          List.replicate n b) =
      some (.falling 0) := by
  rw [scan_append]
  rw [List.replicate_succ]
  simp only [scan, step]
  have ha :=
    scan_rising_replicate_a 0 n
  rw [ha]
  simp only
  simpa using scan_rising_replicate_b_partial hn

theorem block_mem
    (n : Nat) :
    List.replicate n a ++
        List.replicate n b ∈ Language := by
  exact scan_block n

theorem two_blocks_mem
    (n : Nat) :
    (List.replicate n a ++
        List.replicate n b) ++
      (List.replicate n a ++
        List.replicate n b) ∈ Language := by
  change
    scan .zero
        ((List.replicate n a ++
            List.replicate n b) ++
          (List.replicate n a ++
            List.replicate n b)) =
      some .zero
  rw [scan_append, scan_block]
  exact scan_block n

theorem replicate_succ_right
    (s : Symbol)
    (n : Nat) :
    List.replicate n s ++ [s] =
      List.replicate (n + 1) s := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [List.replicate_succ]
      rw [List.replicate_succ]
      simp only [List.cons_append]
      exact congrArg (fun w => s :: w) ih

theorem a_block_b_mem
    (n : Nat) :
    a ::
        (List.replicate n a ++
          List.replicate n b) ++ [b]
      ∈ Language := by
  have hb :
      List.replicate n b ++ [b] =
        List.replicate (n + 1) b :=
    replicate_succ_right b n
  have heq :
      a ::
          (List.replicate n a ++
            List.replicate n b) ++ [b]
        =
      List.replicate (n + 1) a ++
        List.replicate (n + 1) b := by
    calc
      a ::
          (List.replicate n a ++
            List.replicate n b) ++ [b]
        =
      a ::
          (List.replicate n a ++
            (List.replicate n b ++ [b])) := by
          simp [List.append_assoc]
      _ =
      a ::
          (List.replicate n a ++
            List.replicate (n + 1) b) := by
          rw [hb]
      _ =
      List.replicate (n + 1) a ++
        List.replicate (n + 1) b := by
          rw [List.replicate_succ]
          rfl
  rw [heq]
  exact block_mem (n + 1)

theorem a_two_blocks_b_not_mem
    {n : Nat}
    (hn : 0 < n) :
    a ::
        ((List.replicate n a ++
            List.replicate n b) ++
          (List.replicate n a ++
            List.replicate n b)) ++ [b]
      ∉ Language := by
  intro hmem
  change
    scan .zero
      (a ::
        ((List.replicate n a ++
            List.replicate n b) ++
          (List.replicate n a ++
            List.replicate n b)) ++ [b]) =
      some .zero at hmem
  have hb :
      List.replicate n b ++ [b] =
        List.replicate (n + 1) b :=
    replicate_succ_right b n
  have hshape :
      a ::
          ((List.replicate n a ++
              List.replicate n b) ++
            (List.replicate n a ++
              List.replicate n b)) ++ [b]
        =
      (List.replicate (n + 1) a ++
          List.replicate n b) ++
        (List.replicate n a ++
          List.replicate (n + 1) b) := by
    calc
      a ::
          ((List.replicate n a ++
              List.replicate n b) ++
            (List.replicate n a ++
              List.replicate n b)) ++ [b]
        =
      (a :: List.replicate n a) ++
        List.replicate n b ++
        (List.replicate n a ++
          (List.replicate n b ++ [b])) := by
            simp [List.append_assoc]
      _ =
      (a :: List.replicate n a) ++
        List.replicate n b ++
        (List.replicate n a ++
          List.replicate (n + 1) b) := by
            rw [hb]
      _ =
      (List.replicate (n + 1) a ++
          List.replicate n b) ++
        (List.replicate n a ++
          List.replicate (n + 1) b) := by
            simpa [List.replicate_succ,
              List.append_assoc]
  rw [hshape] at hmem
  rw [scan_append, scan_bad_prefix hn] at hmem
  cases n with
  | zero =>
      omega
  | succ m =>
      rw [List.replicate_succ] at hmem
      simp [scan, step] at hmem

theorem replicate_split
    (s : Symbol)
    {k n : Nat}
    (hk : k ≤ n) :
    List.replicate k s ++
        List.replicate (n - k) s =
      List.replicate n s := by
  rw [← List.replicate_add]
  congr 1
  omega

theorem replicate_split_right
    (s : Symbol)
    {l n : Nat}
    (hl : l ≤ n) :
    List.replicate (n - l) s ++
        List.replicate l s =
      List.replicate n s := by
  rw [← List.replicate_add]
  congr 1
  omega

def paperS
    (k l : Nat) :
    Word Symbol :=
  let N := max 1 (k + l)
  List.replicate N a ++
    List.replicate N b

def paperT
    (k l : Nat) :
    Word Symbol :=
  let N := max 1 (k + l)
  (List.replicate N a ++
      List.replicate N b) ++
    (List.replicate N a ++
      List.replicate N b)

theorem paper_sameFixedWindowSummary
    (k l : Nat) :
    SameFixedWindowSummary k l
      (paperS k l) (paperT k l) := by
  let N := max 1 (k + l)
  have hkN : k ≤ N := by
    dsimp [N]
    omega
  have hlN : l ≤ N := by
    dsimp [N]
    omega
  by_cases hkl : k + l = 0
  · have hk : k = 0 := by omega
    have hl : l = 0 := by omega
    subst k
    subst l
    exact
      zero_words_sameFixedWindowSummary
        (by simp [paperS])
        (by simp [paperT])
  · have hklpos : 0 < k + l := by omega
    let p : Word Symbol :=
      List.replicate k a
    let q : Word Symbol :=
      List.replicate l b
    let m₁ : Word Symbol :=
      List.replicate (N - k) a ++
        List.replicate (N - l) b
    let m₂ : Word Symbol :=
      List.replicate (N - k) a ++
        List.replicate N b ++
        List.replicate N a ++
        List.replicate (N - l) b
    have hp : p.length = k := by
      simp [p]
    have hq : q.length = l := by
      simp [q]
    have ha :
        List.replicate k a ++
            List.replicate (N - k) a =
          List.replicate N a :=
      replicate_split a hkN
    have hb :
        List.replicate (N - l) b ++
            List.replicate l b =
          List.replicate N b :=
      replicate_split_right b hlN
    have hs :
        paperS k l =
          p ++ m₁ ++ q := by
      dsimp [paperS, p, m₁, q]
      change
        List.replicate N a ++
            List.replicate N b =
          List.replicate k a ++
            (List.replicate (N - k) a ++
              List.replicate (N - l) b) ++
            List.replicate l b
      calc
        List.replicate N a ++
            List.replicate N b
          =
        (List.replicate k a ++
            List.replicate (N - k) a) ++
          (List.replicate (N - l) b ++
            List.replicate l b) := by
              rw [ha, hb]
        _ =
        List.replicate k a ++
            (List.replicate (N - k) a ++
              List.replicate (N - l) b) ++
            List.replicate l b := by
              simp only [List.append_assoc]
    have ht :
        paperT k l =
          p ++ m₂ ++ q := by
      dsimp [paperT, p, m₂, q]
      change
        (List.replicate N a ++
            List.replicate N b) ++
          (List.replicate N a ++
            List.replicate N b) =
        List.replicate k a ++
          (List.replicate (N - k) a ++
            List.replicate N b ++
            List.replicate N a ++
            List.replicate (N - l) b) ++
          List.replicate l b
      calc
        (List.replicate N a ++
            List.replicate N b) ++
          (List.replicate N a ++
            List.replicate N b)
          =
        (List.replicate k a ++
            List.replicate (N - k) a) ++
          List.replicate N b ++
          List.replicate N a ++
          (List.replicate (N - l) b ++
            List.replicate l b) := by
              rw [ha, hb]
              simp only [List.append_assoc]
        _ =
        List.replicate k a ++
          (List.replicate (N - k) a ++
            List.replicate N b ++
            List.replicate N a ++
            List.replicate (N - l) b) ++
          List.replicate l b := by
              simp only [List.append_assoc]
    rw [hs, ht]
    exact
      boundary_words_sameFixedWindowSummary
        hklpos p q m₁ m₂ hp hq

theorem paper_shared_context
    (k l : Nat) :
    HaveSharedContext
      Language
      (paperS k l)
      (paperT k l) := by
  let N := max 1 (k + l)
  exact
    ⟨[], [],
      by
        simpa [paperS] using block_mem N,
      by
        simpa [paperT] using two_blocks_mem N⟩

theorem paperS_ne_nil
    (k l : Nat) :
    paperS k l ≠ [] := by
  let N := max 1 (k + l)
  have hN : 0 < N := by
    dsimp [N]
    omega
  intro hnil
  have hlen :=
    congrArg List.length hnil
  simp [paperS] at hlen

theorem paperT_ne_nil
    (k l : Nat) :
    paperT k l ≠ [] := by
  let N := max 1 (k + l)
  have hN : 0 < N := by
    dsimp [N]
    omega
  intro hnil
  have hlen :=
    congrArg List.length hnil
  simp [paperT] at hlen

theorem not_fixedWindowSubstitutable
    (k l : Nat) :
    ¬ FixedWindowSubstitutable
        k l Language := by
  let N := max 1 (k + l)
  have hN : 0 < N := by
    dsimp [N]
    omega
  apply
    not_fixedWindowSubstitutable_of_distinguishing_context
      k l Language
      (paperS k l)
      (paperT k l)
      (paperS_ne_nil k l)
      (paperT_ne_nil k l)
      (paper_sameFixedWindowSummary k l)
      (paper_shared_context k l)
      [a] [b]
  · change
      a :: paperS k l ++ [b] ∈ Language
    simpa [paperS, N] using a_block_b_mem N
  · change
      a :: paperT k l ++ [b] ∉ Language
    simpa [paperT, N] using
      a_two_blocks_b_not_mem hN

end DeltaStar
end TCS1
end LeanCfgProject
