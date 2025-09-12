/-
  Port of vericoding_dafnybench_0029_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def arraySum (a : Array Int) (b : Array Int) : Array Int :=
  sorry  -- TODO: implement function body

theorem arraySum_spec (a : Array Int) (b : Array Int) (c : Array Int) :=
  (h_0 : a.size==b.size)
  : c.size==a.size ∧ ∀ i:: 0 ≤ i< a.size→ a[i]! + b[i]≠=c[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks