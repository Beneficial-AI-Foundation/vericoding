/-
  Port of vericoding_dafnybench_0202_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

def Abs (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Abs_spec (x : Int) (y : Int) :=
  : y≥0; ∧ x≥0 → x == y; ∧ x<0 → -x == y; ∧ y == abs(x); // use this instead of line 3,4
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def MultiReturn (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem MultiReturn_spec (x : Int) (y : Int) (more : Int) :=
  (h_0 : y≥0;)
  : less ≤ x ≤ more;
  := by
  sorry  -- TODO: implement proof

def Max (x : Int) (y : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Max_spec (x : Int) (y : Int) (a : Int) :=
  : a == x ∨ a == y; ∧ x > y → a == x; ∧ x ≤ y → a == y;
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks