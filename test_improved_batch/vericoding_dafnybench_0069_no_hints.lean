/-
  Port of vericoding_dafnybench_0069_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  : fresh(a) ∧ a.size == |xs| ∧ ∀ i :: 0 ≤ i < |xs| → a[i]! == xs[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks