/-
  Port of vericoding_dafnybench_0457_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Valid  : Bool :=
  ∀ m n, 0 ≤ m < n < thresholds.size → thresholds[m]! ≤ thresholds[n]!

def RoundDown (k : Int) : Int :=
  sorry  -- TODO: implement function body

theorem RoundDown_spec (k : Int) (r : Int) :=
  (h_0 : Valid())
  : -1 ≤ r < thresholds.size ∧ ∀ m :: r < m < thresholds.size → k < thresholds[m]! ∧ 0 ≤ r → thresholds[r]! ≤ k
  := by
  sorry  -- TODO: implement proof

def RoundUp (k : Int) : Int :=
  sorry  -- TODO: implement function body

theorem RoundUp_spec (k : Int) (r : Int) :=
  (h_0 : Valid())
  : 0 ≤ r ≤ thresholds.size ∧ ∀ m :: 0 ≤ m < r → thresholds[m]! < k ∧ r < thresholds.size → k ≤ thresholds[r]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks