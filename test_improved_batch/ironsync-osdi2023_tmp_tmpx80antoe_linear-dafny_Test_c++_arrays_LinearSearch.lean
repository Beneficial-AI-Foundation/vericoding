/-
  Port of ironsync-osdi2023_tmp_tmpx80antoe_linear-dafny_Test_c++_arrays_LinearSearch.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def LinearSearch (a : array<uint32>) (len : uint32) (key : uint32) : uint32 :=
  sorry  -- TODO: implement function body

theorem LinearSearch_spec (a : array<uint32>) (len : uint32) (key : uint32) (n : uint32) :=
  (h_0 : a.size == len as Int)
  : 0 ≤ n ≤ len ∧ n == len ∨ a[n]! == key
  := by
  sorry  -- TODO: implement proof


  (h_0 : a ≠ null → len as Int == a.size)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks