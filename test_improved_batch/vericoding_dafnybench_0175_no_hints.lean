/-
  Port of vericoding_dafnybench_0175_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Index (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Index_spec (n : Int) (i : Int) :=
  (h_0 : 1 ≤ n)
  : 0 ≤ i < n
  := by
  sorry  -- TODO: implement proof

def Min (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Min_spec (x : Int) (y : Int) (m : Int) :=
  : m ≤ x ∧ m ≤ y ∧ m == x ∨ m == y
  := by
  sorry  -- TODO: implement proof

def Max (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Max_spec (x : Int) (y : Int) (m : Int) :=
  := by
  sorry  -- TODO: implement proof

def MaxSum (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem MaxSum_spec (x : Int) (y : Int) (s : Int) :=
  : s == x + y ∧ m == if x ≥ y then x else y
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def ReconstructFromMaxSum (s : Int) (m : Int) : Int :=
  sorry  -- TODO: implement function body

theorem ReconstructFromMaxSum_spec (s : Int) (m : Int) (x : Int) :=
  (h_0 : s ≤ 2 * m)
  : s == (x + y) ∧ (m == x ∨ m == y) ∧ x ≤ m ∧ y ≤ m
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks