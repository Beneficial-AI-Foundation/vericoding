/-
  Port of vericoding_dafnybench_0052_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : ∃ i, 0 ≤ i < a.size ∧ P(a[i]!))
  : 0 ≤ n < a.size ∧ P(a[n]!) ∧ ∀ k :: 0 ≤ k < n → !P(a[k]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks