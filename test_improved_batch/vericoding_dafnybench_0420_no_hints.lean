/-
  Port of vericoding_dafnybench_0420_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def twoSum (nums : seq<int>) (target : Int) : (int :=
  sorry  -- TODO: implement function body

theorem twoSum_spec (nums : seq<int>) (target : Int) (pair : (int) :=
  (h_0 : ∃ i, j :: correct_pair((i, j), nums, target))
  : correct_pair(pair, nums, target)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks