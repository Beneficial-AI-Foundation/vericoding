// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn summing_pair(i: nat, j: nat, nums: Seq<int>, target: int) -> bool
    recommends 
        i < nums.len(),
        j < nums.len(),
{
    i != j && nums[i as int] + nums[j as int] == target
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No change needed, fixing compilation error in code section. */
spec fn is_the_solution_pair(i: nat, j: nat, nums: Seq<int>, target: int) -> bool {
    i < j < nums.len() &&
    summing_pair(i, j, nums, target) &&
    forall|l: nat, m: nat| l < m < nums.len() && l != i && m != j ==> !summing_pair(l, m, nums, target)
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
    /* code modified by LLM (iteration 5): Fixed incorrect nat to usize conversion. Used 'as' cast instead of '.to_usize()'. */
    let (i, j) = choose|i: nat, j: nat| is_the_solution_pair(i, j, nums, target);
    (i as usize, j as usize)
}
// </vc-code>

}
fn main() {}