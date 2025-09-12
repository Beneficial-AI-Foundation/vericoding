/-
  Port of vericoding_dafnybench_0573_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ContainsConsecutiveNumbers (a : Array Int) : Bool :=
  sorry  -- TODO: implement function body

theorem ContainsConsecutiveNumbers_spec (a : Array Int) (result : Bool) :=
  (h_0 : a.size>0)
  : result <→ (∃ i, 0 ≤ i < a.size - 1 ∧ a[i]! + 1 == a[i + 1])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks