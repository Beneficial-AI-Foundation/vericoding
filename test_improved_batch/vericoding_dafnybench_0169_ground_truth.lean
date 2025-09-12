/-
  Port of vericoding_dafnybench_0169_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  : 0 ≤ n ≤ a.size ∧ n == a.size ∨ P(a[n]!) ∧ ∀ i :: 0 ≤ i < n → !P(a[i]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks