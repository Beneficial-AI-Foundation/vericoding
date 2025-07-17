// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn summingPair(i: nat, j: nat, nums: Seq<int>, target: int)
  requires i < |nums|
  requires j < |nums|
{
  i != j && nums[i] + nums[j] == target
}


// SPEC
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
  requires exists i: nat, j: nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l < m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
  ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target) -> bool {
    
}

spec fn spec_twoSum(nums: Seq<int>, target: int) -> pair: (nat, nat)
    requires
        exists |i: nat, j: nat| i < j < nums.len() && summingPair(i, j, nums, target) && forall |l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures
        0 <= pair.0 < nums.len() && 0 <= pair.1 < nums.len() && summingPair(pair.0, pair.1, nums, target)
;

proof fn lemma_twoSum(nums: Seq<int>, target: int) -> (pair: (nat, nat))
    requires
        exists |i: nat, j: nat| i < j < nums.len() && summingPair(i, j, nums, target) && forall |l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures
        0 <= pair.0 < nums.len() && 0 <= pair.1 < nums.len() && summingPair(pair.0, pair.1, nums, target)
{
    (0, 0)
}

}