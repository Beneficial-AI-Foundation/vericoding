/-
  Port of vericoding_dafnybench_0212_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : a.size > 0)
  : ∀ i :: 0 ≤ i < a.size → a[i]! == old(a[i]!) + 1
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks