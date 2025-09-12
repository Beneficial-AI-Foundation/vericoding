/-
  Port of Dafny_Verify_tmp_tmphq7j0row_dataset_error_data_real_error_IsEven_success_1_is_even.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def even (n : Int) : Bool :=
  sorry  -- TODO: implement function body

def is_even (n : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem is_even_spec (n : Int) (r : Bool) :=
  (h_0 : n ≥ 0;)
  : r <→ even(n);
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks