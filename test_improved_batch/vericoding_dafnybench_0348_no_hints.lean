/-
  Port of vericoding_dafnybench_0348_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def peasantMult (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem peasantMult_spec (a : Int) (b : Int) (r : Int) :=
  (h_0 : b > 0)
  : r == a * b
  := by
  sorry  -- TODO: implement proof

def euclidianDiv (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem euclidianDiv_spec (a : Int) (b : Int) (q : Int) :=
  (h_0 : a ≥ 0)
  (h_1 : b > 0)
  : a == b * q + r
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks