/-
  Port of vericoding_dafnybench_0575_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Min (a : seq<int>) : Int :=
  sorry  -- TODO: implement complex function body

def Max (a : seq<int>) : Int :=
  sorry  -- TODO: implement complex function body

def SumMinMax (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem SumMinMax_spec (a : Array Int) (sum : Int) :=
  (h_0 : a.size > 0)
  : sum == Max(a[..]) + Min(a[..])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks