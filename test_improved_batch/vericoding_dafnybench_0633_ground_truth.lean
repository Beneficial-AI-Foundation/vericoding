/-
  Port of vericoding_dafnybench_0633_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsMonthWith30Days (month : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsMonthWith30Days_spec (month : Int) (result : Bool) :=
  (h_0 : 1 ≤ month ≤ 12)
  : result <→ month == 4 ∨ month == 6 ∨ month == 9 ∨ month == 11
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks