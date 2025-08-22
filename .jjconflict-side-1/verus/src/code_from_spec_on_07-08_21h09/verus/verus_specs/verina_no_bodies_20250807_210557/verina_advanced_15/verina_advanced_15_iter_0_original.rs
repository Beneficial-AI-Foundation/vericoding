use vstd::prelude::*;

verus! {

spec fn increasing_triplet_precond(nums: Seq<i32>) -> bool {
    true
}

fn increasing_triplet(nums: Vec<i32>) -> (result: bool)
    requires increasing_triplet_precond(nums@)
{
    return false;  // TODO: Remove this line and implement the function body
}

fn loop_search(nums: &Vec<i32>, start: usize, first: i32, second: i32) -> (result: bool)
    requires start <= nums.len()
    decreases nums.len() - start
{
    return false;  // TODO: Remove this line and implement the function body
}

spec fn increasing_triplet_postcond(nums: Seq<i32>, result: bool) -> bool {
    if result {
        exists|i: int, j: int, k: int| 
            0 <= i < j && j < k && k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k]
    } else {
        forall|i: int, j: int, k: int| 
            (0 <= i < j && j < k && k < nums.len()) ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k])
    }
}

}

fn main() {}