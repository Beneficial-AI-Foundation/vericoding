/-
  Port of Dafny_Verify_tmp_tmphq7j0row_dataset_bql_exampls_Min_min.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def min (a : Array Int) (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem min_spec (a : Array Int) (n : Int) (min : Int) :=
  (h_0 : 0 < n ≤ a.size;)
  : (∃ i : Int :: 0 ≤ i ∧ i < n ∧ a[i]! == min); ∧ (∀ i : Int, 0 ≤ i ∧ i < n → a[i]! ≥ min);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks