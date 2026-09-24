import LeanCfgProject.TCS1.LinearSeparatorTyping

/-!
# TCS #1 v77: distribution arithmetic for the separator language

This module formalizes the arithmetic core of the revised Section 8.1 proof.
For a one-center factor a^i z b^j, membership after a pure-power context
(a^m,b^n) is characterized exactly by the two boundary exponents.

This is the Lean form of the manuscript's balance/parity calculation:
the e-branch depends only on the exponent difference, while the c/d branch
adds the parity condition on the left exponent.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- A possibly unbalanced one-center word a^i z b^j. -/
def lpmOneCenter
    (i : Nat) (z : LpmSymbol) (j : Nat) :
    Word LpmSymbol :=
  List.replicate i a ++ [z] ++ List.replicate j b

@[simp] theorem lpmOneCenter_balanced
    (n : Nat) (z : LpmSymbol) :
    lpmOneCenter n z n = lpmCore n z := by
  rfl

/-- Exact membership for the even-parity center c. -/
theorem lpmOneCenter_c_mem_iff
    (i j : Nat) :
    lpmOneCenter i c j ∈ LpmLanguage ↔
      i = j ∧ i % 2 = 0 := by
  constructor
  · rintro ⟨n, z', hword, hacc⟩
    cases z' with
    | a =>
        simp [LpmAccepted] at hacc
    | b =>
        simp [LpmAccepted] at hacc
    | c =>
        have ha := congrArg (List.count a) hword
        have hb := congrArg (List.count b) hword
        have hin : i = n := by
          simpa [lpmOneCenter, lpmCore, List.count_replicate] using ha
        have hjn : j = n := by
          simpa [lpmOneCenter, lpmCore, List.count_replicate] using hb
        refine ⟨hin.trans hjn.symm, ?_⟩
        simpa [LpmAccepted, hin] using hacc
    | d =>
        have hc := congrArg (List.count c) hword
        exfalso
        simpa [lpmOneCenter, lpmCore, List.count_replicate] using hc
    | e =>
        have hc := congrArg (List.count c) hword
        exfalso
        simpa [lpmOneCenter, lpmCore, List.count_replicate] using hc
  · rintro ⟨rfl, heven⟩
    simpa [lpmOneCenter, lpmCore] using
      (lpmCore_mem_iff i c).2 heven

/-- Exact membership for the odd-parity center d. -/
theorem lpmOneCenter_d_mem_iff
    (i j : Nat) :
    lpmOneCenter i d j ∈ LpmLanguage ↔
      i = j ∧ i % 2 = 1 := by
  constructor
  · rintro ⟨n, z', hword, hacc⟩
    cases z' with
    | a =>
        simp [LpmAccepted] at hacc
    | b =>
        simp [LpmAccepted] at hacc
    | c =>
        have hd := congrArg (List.count d) hword
        exfalso
        simpa [lpmOneCenter, lpmCore, List.count_replicate] using hd
    | d =>
        have ha := congrArg (List.count a) hword
        have hb := congrArg (List.count b) hword
        have hin : i = n := by
          simpa [lpmOneCenter, lpmCore, List.count_replicate] using ha
        have hjn : j = n := by
          simpa [lpmOneCenter, lpmCore, List.count_replicate] using hb
        refine ⟨hin.trans hjn.symm, ?_⟩
        simpa [LpmAccepted, hin] using hacc
    | e =>
        have hd := congrArg (List.count d) hword
        exfalso
        simpa [lpmOneCenter, lpmCore, List.count_replicate] using hd
  · rintro ⟨rfl, hodd⟩
    simpa [lpmOneCenter, lpmCore] using
      (lpmCore_mem_iff i d).2 hodd

/-- Exact membership for the parity-free center e. -/
theorem lpmOneCenter_e_mem_iff
    (i j : Nat) :
    lpmOneCenter i e j ∈ LpmLanguage ↔
      i = j := by
  constructor
  · rintro ⟨n, z', hword, hacc⟩
    cases z' with
    | a =>
        simp [LpmAccepted] at hacc
    | b =>
        simp [LpmAccepted] at hacc
    | c =>
        have heq := congrArg (List.count e) hword
        exfalso
        simpa [lpmOneCenter, lpmCore, List.count_replicate] using heq
    | d =>
        have heq := congrArg (List.count e) hword
        exfalso
        simpa [lpmOneCenter, lpmCore, List.count_replicate] using heq
    | e =>
        have ha := congrArg (List.count a) hword
        have hb := congrArg (List.count b) hword
        have hin : i = n := by
          simpa [lpmOneCenter, lpmCore, List.count_replicate] using ha
        have hjn : j = n := by
          simpa [lpmOneCenter, lpmCore, List.count_replicate] using hb
        exact hin.trans hjn.symm
  · intro hij
    subst j
    simpa [lpmOneCenter, lpmCore] using
      lpm_e_mem i

/--
Adding a pure-a context on the left and a pure-b context on the right just
adds to the two exponents.
-/
theorem lpm_power_context_word
    (m n i j : Nat) (z : LpmSymbol) :
    List.replicate m a ++
        lpmOneCenter i z j ++
        List.replicate n b =
      lpmOneCenter (m + i) z (j + n) := by
  unfold lpmOneCenter
  have ha :
      List.replicate m a ++ List.replicate i a =
        List.replicate (m + i) a :=
    (List.replicate_add m i a).symm
  have hb :
      List.replicate j b ++ List.replicate n b =
        List.replicate (j + n) b :=
    (List.replicate_add j n b).symm
  calc
    List.replicate m a ++
          (List.replicate i a ++ [z] ++ List.replicate j b) ++
          List.replicate n b =
        (List.replicate m a ++ List.replicate i a) ++
          [z] ++
          (List.replicate j b ++ List.replicate n b) := by
            simp only [List.append_assoc]
    _ =
        List.replicate (m + i) a ++
          [z] ++
          List.replicate (j + n) b := by
            rw [ha, hb]



end TCS1
end LeanCfgProject
