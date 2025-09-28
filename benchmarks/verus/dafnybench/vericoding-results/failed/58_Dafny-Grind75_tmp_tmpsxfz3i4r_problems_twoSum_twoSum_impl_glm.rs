use vstd::prelude::*;

verus! {

spec fn summing_pair(i: nat, j: nat, nums: Seq<int>, target: int) -> bool
    recommends 
        i < nums.len(),
        j < nums.len(),
{
    i != j && nums[i as int] + nums[j as int] == target
}

// <vc-helpers>
proof fn lemma_unique_pair_exists(nums: Seq<int>, target: int)
    requires exists|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target)
    ensures exists|i: nat, j: nat| i < nums.len() && j < nums.len() && i != j && nums[i as int] + nums[j as int] == target
{
    let (i0, j0) = choose|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target);
    assert(i0 < nums.len() && j0 < nums.len());
    assert(i0 != j0);
    assert(nums[i0 as int] + nums[j0 as int] == target);
}
// </vc-helpers>

// <vc-spec>
fn two_sum(nums: Seq<int>, target: int) -> (pair: (usize, usize))
    requires exists|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target)
    ensures 
        0 <= pair.0 < nums.len() && 
        0 <= pair.1 < nums.len() && 
        summing_pair(pair.0 as nat, pair.1 as nat, nums, target)
// </vc-spec>
// <vc-code>
{
    lemma_unique_pair_exists(nums, target);
    let (i, j) = choose|i: nat, j: nat|
        i < nums.len() && j < nums.len() && i != j && nums[i as int] + nums[j as int] == target;
    (i as usize, j as usize)
}
// </vc-code>

fn main() {
}

}