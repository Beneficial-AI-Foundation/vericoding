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
proof fn exists_witness_lemma(nums: Seq<int>, target: int) -> (pair: (nat, nat))
    requires exists|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target)
    ensures 
        pair.0 < pair.1 < nums.len() && 
        summing_pair(pair.0, pair.1, nums, target)
{
    choose|i: nat, j: nat| i < j < nums.len() && summing_pair(i, j, nums, target) && forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target)
}

proof fn nat_to_usize_bounds(n: nat, len: nat)
    requires n < len
    ensures n < usize::MAX
{
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
    let witness = exists_witness_lemma(nums, target);
    let i = witness.0;
    let j = witness.1;
    
    assert(i < j < nums.len());
    assert(summing_pair(i, j, nums, target));
    
    proof {
        nat_to_usize_bounds(i, nums.len());
        nat_to_usize_bounds(j, nums.len());
    }
    
    let i_usize = i.value_fits(usize::BITS) as usize;
    let j_usize = j.value_fits(usize::BITS) as usize;
    
    (i_usize, j_usize)
}
// </vc-code>

fn main() {
}

}