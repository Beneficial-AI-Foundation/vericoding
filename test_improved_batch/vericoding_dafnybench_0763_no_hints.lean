/-
  Port of vericoding_dafnybench_0763_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  : 0 ≤ r → r < a.size ∧ a[r]! == x ∧ r < 0 → ∀ i :: 0 ≤ i < a.size → a[i]! ≠ x
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks