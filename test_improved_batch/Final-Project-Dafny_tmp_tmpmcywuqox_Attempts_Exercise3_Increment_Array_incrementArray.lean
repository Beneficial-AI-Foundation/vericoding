/-
  Port of Final-Project-Dafny_tmp_tmpmcywuqox_Attempts_Exercise3_Increment_Array_incrementArray.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : a.size > 0)
  : ∀ i :: 0 ≤ i < a.size → a[i]! == old(a[i]!) + 1
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks