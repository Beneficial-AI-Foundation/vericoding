/-
  Port of vericoding_dafnybench_0109_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def twoSum (nums : number[]) (target : number) : number :=
  sorry  -- TODO: implement function body

def twoSum (nums : seq<int>) (target : Int) : (nat :=
  sorry  -- TODO: implement function body

theorem twoSum_spec (nums : seq<int>) (target : Int) (pair : (nat) :=
  (h_0 : ∃ i:nat,j:nat :: i < j < |nums| ∧ summingPair(i, j, nums, target) ∧ ∀ l: nat, m: nat :: l <  m < |nums| ∧ l ≠ i ∧ m ≠ j → !summingPair(l, m, nums, target))
  : 0 ≤ pair.0 < |nums| ∧ 0 ≤ pair.1 < |nums| ∧ summingPair(pair.0, pair.1, nums, target)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks