// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn summingPair(i: nat, j: nat, nums: Seq<int>, target: int)
    requires i < |nums|
    requires j < |nums|
{
    i != j &&  nums[i] + nums[j] == target
}

// SPEC 
method twoSum(nums: seq<int>, target: int) returns (pair: (nat, nat))
    requires exists i: nat, j: nat :: i < j < |nums| && summingPair(i, j, nums, target) && forall l: nat, m: nat :: l <  m < |nums| && l != i && m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < |nums| && 0 <= pair.1 < |nums| && summingPair(pair.0, pair.1, nums, target) -> bool {
    
}

fn twoSum(nums: Seq<int>, target: int) -> pair: (nat, nat)
    requires exists i:nat,j:nat :: i < j < nums.len() and summingPair(i, j, nums, target) and forall l: nat, m: nat :: l <  m < nums.len() and l != i and m != j ==> !summingPair(l, m, nums, target)
    ensures 0 <= pair.0 < nums.len() and 0 <= pair.1 < nums.len() and summingPair(pair.0, pair.1, nums, target)
{
}

}