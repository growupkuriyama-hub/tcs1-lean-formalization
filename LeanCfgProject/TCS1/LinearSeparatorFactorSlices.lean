import LeanCfgProject.TCS1.LinearSeparatorExample

/-!
# TCS #1 v77: factor slices of separator words

This file begins the structural part of the Section 8.1 fixed-h proof.
A factor occurring in a terminal context is first identified with the
corresponding drop/take slice of the ambient canonical word.  Later lemmas
classify those slices relative to the unique center position.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- A factor in an explicit two-sided context is the corresponding slice. -/
theorem factor_eq_drop_take_of_context
    {u x v w : Word LpmSymbol}
    (h : u ++ x ++ v = w) :
    x = (w.drop u.length).take x.length := by
  rw [← h]
  simp [List.append_assoc]

end TCS1
end LeanCfgProject
