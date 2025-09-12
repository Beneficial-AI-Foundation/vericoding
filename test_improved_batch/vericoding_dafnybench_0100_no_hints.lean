/-
  Port of vericoding_dafnybench_0100_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def min (v : Array Int) (i : Int) : Int :=
  else if (v[i-1]≤min(v,i-1)) then v[i-1] else min(v,i-1)

def countMin (v : Array Int) (x : Int) (i : Int) : Int :=
  sorry  -- TODO: implement complex function body

def mCountMin (v : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem mCountMin_spec (v : Array Int) (c : Int) :=
  (h_0 : v.size>0)
  : c==countMin(v,min(v,v.size),v.size)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks