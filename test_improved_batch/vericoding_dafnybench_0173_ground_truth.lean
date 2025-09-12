/-
  Port of vericoding_dafnybench_0173_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Average (a : Int) (b : Int) : Int :=
  (a + b) / 2

def TripleConditions (x : Int) : Int :=
  sorry  -- TODO: implement function body

theorem TripleConditions_spec (x : Int) (r : Int) :=
  : r == 3 * x
  := by
  sorry  -- TODO: implement proof


  : Average(r, 3 * x) == 3 * x ∧ r == 3 * x
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks