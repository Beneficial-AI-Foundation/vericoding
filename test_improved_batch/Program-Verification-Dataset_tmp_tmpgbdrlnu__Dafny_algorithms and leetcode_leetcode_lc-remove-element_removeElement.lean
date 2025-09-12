/-
  Port of Program-Verification-Dataset_tmp_tmpgbdrlnu__Dafny_algorithms and leetcode_leetcode_lc-remove-element_removeElement.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def removeElement (nums : Array Int) (val : Int) : Int :=
  sorry  -- TODO: implement function body

theorem removeElement_spec (nums : Array Int) (val : Int) (i : Int) :=
  : ∀ k :: 0 < k < i < nums.size → nums[k]! ≠ val
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks