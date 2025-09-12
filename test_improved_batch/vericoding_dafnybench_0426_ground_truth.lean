/-
  Port of vericoding_dafnybench_0426_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Sum (xs : seq<int>) : Int :=
  sorry  -- TODO: implement function body

def SumArray (xs : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem SumArray_spec (xs : Array Int) (s : Int) :=
  : s == Sum(xs[..])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks