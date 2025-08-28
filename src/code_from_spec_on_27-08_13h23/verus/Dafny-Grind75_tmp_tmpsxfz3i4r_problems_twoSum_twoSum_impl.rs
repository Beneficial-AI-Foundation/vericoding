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
spec fn exists_pair(nums: Seq<int>, target: int, i: nat, j: nat) -> bool {
    i < j < nums.len() && summing_pair(i, j, nums, target)
}

proof fn unique_pair_lemma(nums: Seq<int>, target: int)
    requires exists|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target)
    ensures exists|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target)
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn two_sum(nums: Seq<int>, target: int) -> (pair: (usize, usize))
    requires exists|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target)
    ensures 
        0 <= pair.0 < nums.len() && 
        0 <= pair.1 < nums.len() && 
        summing_pair(pair.0 as nat, pair.1 as nat, nums, target)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn two_sum(nums: Seq<int>, target: int) -> (pair: (usize, usize))
    requires exists|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target)
    ensures 
        0 <= pair.0 < nums.len() && 
        0 <= pair.1 < nums.len() && 
        summing_pair(pair.0 as nat, pair.1 as nat, nums, target)
{
    let mut i: usize = 0;
    let mut j: usize = 1;
    let mut found = false;
    while i < nums.len() && !found
        invariant
            0 <= i < nums.len(),
            forall|k: nat| k <= i ==> forall|l: nat| k < l < nums.len() ==> !summing_pair(k, l, nums, target)
    {
        j = i + 1;
        while j < nums.len() && !found
            invariant
                0 <= i < j <= nums.len(),
                forall|k: nat| k <= i ==> forall|l: nat| k < l < nums.len() ==> !summing_pair(k, l, nums, target),
                forall|l: nat| i < l < j ==> !summing_pair(i as nat, l, nums, target)
        {
            if nums[i] + nums[j] == target {
                found = true;
            } else {
                j = j + 1;
            }
        }
        if !found {
            i = i + 1;
        }
    }
    (i, j)
}
// </vc-code>

fn main() {
}

}