/-
  Port of vericoding_dafnybench_0025_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def append (a : Array Int) (b : Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem append_spec (a : Array Int) (b : Int) (c : Array Int) :=
  :  a[..] + [b] == c[..]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks