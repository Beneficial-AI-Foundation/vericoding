/-
  Port of vericoding_dafnybench_0100_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def min (v : Array Int) (i : Int) : Int :=
  sorry  -- TODO: implement function body

def countMin (v : Array Int) (x : Int) (i : Int) : Int :=
  sorry  -- TODO: implement function body

def mCountMin (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mCountMin_spec (v : Array Int) (c : Int) :=
  (h_0 : v.size>0)
  : c==countMin(v,min(v,v.size),v.size)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks