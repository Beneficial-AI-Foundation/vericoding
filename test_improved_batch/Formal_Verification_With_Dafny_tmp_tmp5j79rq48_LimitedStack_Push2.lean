/-
  Port of Formal_Verification_With_Dafny_tmp_tmp5j79rq48_LimitedStack_Push2.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  (h_0 : Valid() ∧ !Empty();)
  : Valid(); ∧ ∀ i : Int, 0 ≤ i < capacity - 1 → arr[i]! == old(arr[i + 1]); ∧ top == old(top) - 1;
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks