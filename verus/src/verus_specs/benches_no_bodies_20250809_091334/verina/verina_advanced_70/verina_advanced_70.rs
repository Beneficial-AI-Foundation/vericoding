use vstd::prelude::*;

verus! {

spec fn semi_ordered_permutation_precond(nums: Seq<int>) -> bool {
    true
}

spec fn index_of_seq(nums: Seq<int>, target: int) -> int
    decreases nums.len(),
{
    if nums.len() == 0 {
        0
    } else if nums[0] == target {
        0
    } else {
        1 + index_of_seq(nums.subrange(1, nums.len() as int), target)
    }
}

spec fn semi_ordered_permutation_postcond(nums: Seq<int>, result: int) -> bool {
    let n = nums.len();
    let pos1 = index_of_seq(nums, 1);
    let posn = index_of_seq(nums, n as int);
    if pos1 > posn {
        pos1 + n == result + 2 + posn
    } else {
        pos1 + n == result + 1 + posn
    }
}

fn semi_ordered_permutation(nums: Vec<i32>) -> (result: i32)
    requires
        nums.len() > 0,
        nums.len() <= 1000,
        semi_ordered_permutation_precond(nums@.map(|i, x| x as int)),
    ensures
        semi_ordered_permutation_postcond(nums@.map(|i, x| x as int), result as int),
{
    return 0;  // TODO: Remove this line and implement the function body
}

fn index_of_exec(nums: &Vec<i32>, target: i32) -> (result: usize)
    requires
        nums.len() > 0,
    ensures
        result < nums.len(),
{
    return 0;  // TODO: Remove this line and implement the function body
}

proof fn semi_ordered_permutation_spec_satisfied(nums: Seq<int>, result: int)
    requires
        nums.len() > 0,
        nums.len() <= 1000,
        semi_ordered_permutation_precond(nums),
    ensures
        semi_ordered_permutation_postcond(nums, result) ==> 
            semi_ordered_permutation_postcond(nums, result),
{
    assume(false);  // TODO: Remove this line and implement the proof
}

}

fn main() {}