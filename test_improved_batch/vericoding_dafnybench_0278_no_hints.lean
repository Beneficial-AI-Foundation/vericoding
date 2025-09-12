/-
  Port of vericoding_dafnybench_0278_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : a ≠ null ∧ a.size > 0)
  (h_1 : ∀ x, y :: cmp.requires(x, y))
  (h_2 : ∀ x, y :: cmp(x, y) ∨ cmp(y, x);)
  (h_3 : ∀ x, y, z :: cmp(x, y) ∧ cmp(y, z) → cmp(x, z);)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks