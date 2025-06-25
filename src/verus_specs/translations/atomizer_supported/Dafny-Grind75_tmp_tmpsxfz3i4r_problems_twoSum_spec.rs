// ATOM 
spec fn summingPair(i: nat, j: nat, nums: Seq<int>, target: int) -> bool
    recommends(i < nums.len())
    recommends(j < nums.len())
{
    i != j && nums[i] + nums[j] == target
}

// SPEC 
pub fn twoSum(nums: Seq<int>, target: int) -> (pair: (nat, nat))
    requires(exists|i: nat, j: nat| i < j < nums.len() && summingPair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summingPair(l, m, nums, target))
    ensures(0 <= pair.0 < nums.len() && 0 <= pair.1 < nums.len() && summingPair(pair.0, pair.1, nums, target))
{
}