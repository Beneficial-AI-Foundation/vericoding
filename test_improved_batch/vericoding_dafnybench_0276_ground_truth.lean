/-
  Port of vericoding_dafnybench_0276_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : a ≠ null)
  (h_1 : ∀ j :: 0 ≤ j < a.size → f.requires(j))
  (h_2 : ∀ j :: 0 ≤ j < a.size → a !in f.reads(j))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks