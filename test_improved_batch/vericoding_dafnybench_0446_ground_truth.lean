/-
  Port of vericoding_dafnybench_0446_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def M (N : Int) (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem M_spec (N : Int) (a : Array Int) (sum : Int) :=
  (h_0 : 0 ≤ N ∧ a.size == N ∧ (∀ k :: 0 ≤ k ∧ k < N → 0 ≤ a[k]!);)
  : sum ≤ N * max;
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks