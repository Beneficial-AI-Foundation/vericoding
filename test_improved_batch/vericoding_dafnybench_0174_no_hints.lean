/-
  Port of vericoding_dafnybench_0174_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Average (a : Int) (b : Int) : Int :=
  (a + b) / 2

def F  : Int :=
  sorry  -- TODO: implement function body

def Triple1 (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Triple1_spec (x : Int) (r : Int) :=
  : r == 3 * x
  := by
  sorry  -- TODO: implement proof

def M  : Int :=
  sorry  -- TODO: implement function body

theorem M_spec (r : Int) :=
  : r == 29
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

def MyMethod (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem MyMethod_spec (x : Int) (y : Int) :=
  (h_0 : 10 ≤ x)
  : 25 ≤ y
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks