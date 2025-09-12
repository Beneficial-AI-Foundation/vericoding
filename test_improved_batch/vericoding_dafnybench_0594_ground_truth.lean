/-
  Port of vericoding_dafnybench_0594_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Min (a : seq<int>) : Int :=
  sorry  -- TODO: implement complex function body

def Max (a : seq<int>) : Int :=
  sorry  -- TODO: implement complex function body

def DifferenceMinMax (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem DifferenceMinMax_spec (a : Array Int) (diff : Int) :=
  (h_0 : a.size > 0)
  : diff == Max(a[..]) - Min(a[..])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks