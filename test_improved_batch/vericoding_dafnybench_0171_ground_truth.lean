/-
  Port of vericoding_dafnybench_0171_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def mult (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem mult_spec (a : Int) (b : Int) (x : Int) :=
  (h_0 : a ≥ 0 ∧ b ≥ 0)
  : x == a * b
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks