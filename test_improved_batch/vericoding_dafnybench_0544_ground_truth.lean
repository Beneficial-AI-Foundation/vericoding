/-
  Port of vericoding_dafnybench_0544_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ToCharArray (s : String) : Array Char :=
  sorry  -- TODO: implement function body

theorem ToCharArray_spec (s : String) (a : Array Char) :=
  : a.size == |s| ∧ ∀ i :: 0 ≤ i < |s| → a[i]! == s[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks