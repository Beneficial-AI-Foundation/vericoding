/-
  Port of vericoding_dafnybench_0610_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindMedian (a : Array Int) (b : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem FindMedian_spec (a : Array Int) (b : Array Int) (median : Int) :=
  (h_0 : a ≠ null ∧ b ≠ null)
  (h_1 : a.size == b.size)
  (h_2 : a.size > 0)
  (h_3 : ∀ i :: 0 ≤ i < a.size - 1 → a[i]! ≤ a[i + 1])
  (h_4 : ∀ i :: 0 ≤ i < b.size - 1 → b[i]! ≤ b[i + 1])
  : median == if (a.size % 2 == 0) then (a[a.size / 2 - 1] + b[0]!) / 2 else a[a.size / 2]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks