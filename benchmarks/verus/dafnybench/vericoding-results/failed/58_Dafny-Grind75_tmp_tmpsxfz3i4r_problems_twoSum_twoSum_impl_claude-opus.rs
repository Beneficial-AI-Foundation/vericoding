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
    let ghost (witness_i, witness_j): (nat, nat) = choose|i: nat, j: nat| 
        i < j < nums.len() && summing_pair(i, j, nums, target) && 
        forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target);
    
    for i in 0..nums.len() as usize
        invariant
            forall|l: nat, m: nat| l < m && m <= i && summing_pair(l, m, nums, target) ==> 
                l == witness_i && m == witness_j
    {
        for j in (i + 1)..nums.len() as usize
            invariant
                i < nums.len(),
                forall|l: nat, m: nat| l < m && m <= i && summing_pair(l, m, nums, target) ==> 
                    l == witness_i && m == witness_j,
                forall|m: nat| (i as nat) < m && m <= j && summing_pair(i as nat, m, nums, target) ==> 
                    (i as nat) == witness_i && m == witness_j
        {
            if nums[i as int] + nums[j as int] == target {
                proof {
                    assert(summing_pair(i as nat, j as nat, nums, target));
                    assert((i as nat) < (j as nat));
                    assert((i as nat) == witness_i && (j as nat) == witness_j);
                }
                return (i, j);
            }
        }
    }
    
    proof {
        assert(witness_i < witness_j < nums.len());
        assert(summing_pair(witness_i, witness_j, nums, target));
        assert(forall|l: nat, m: nat| l < m < nums.len() && summing_pair(l, m, nums, target) ==> 
            l == witness_i && m == witness_j);
        assert(false);
    }
    unreached()
}
// </vc-code>

fn main() {
}

}