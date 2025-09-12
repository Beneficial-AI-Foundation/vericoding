/-
  Port of vericoding_dafnybench_0285_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def yarra (arr : Array Char) : Array Char :=
  sorry  -- TODO: implement function body

theorem yarra_spec (arr : Array Char) (outarr : Array Char) :=
  (h_0 : arr ≠ null ∧ arr.size > 0)
  : outarr ≠ null ∧ arr.size == outarr.size ∧ reversed(arr,outarr)
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks