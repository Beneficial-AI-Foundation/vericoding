/-
  Port of vericoding_dafnybench_0160_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def BinarySearch (a : Array Int) (key : Int) : Int :=
  sorry  -- TODO: implement function body

theorem BinarySearch_spec (a : Array Int) (key : Int) (n : Int) :=
  (h_0 : ∀ i, j :: 0 ≤ i < j < a.size → a[i]! ≤ a[j]!)
  : 0 ≤ n ≤ a.size ∧ ∀ i :: 0 ≤ i < n → a[i]! < key ∧ ∀ i :: n ≤ i < a.size → key ≤ a[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks