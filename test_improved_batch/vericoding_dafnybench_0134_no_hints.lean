/-
  Port of vericoding_dafnybench_0134_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  : 0 ≤ n ≤ a.size ∧ n == a.size ∨ P(a[n]!)
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof


  : 0 ≤ n ≤ a.size ∧ n == a.size ∨ P(a[n]!) ∧ n == a.size → ∀ i :: 0 ≤ i < a.size → !P(a[i]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks