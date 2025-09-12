/-
  Port of vericoding_dafnybench_0388_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sumTo (a : Array Int) (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def sum_array (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem sum_array_spec (a : Array Int) (sum : Int) :=
  (h_0 : a ≠ null;)
  : sum == sumTo(a, a.size);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks