use vstd::prelude::*;

verus! {

spec fn increasing_triplet_precond(nums: Seq<i32>) -> bool {
    true
}

fn increasing_triplet(nums: Vec<i32>) -> (result: bool)
    requires increasing_triplet_precond(nums@)
{
    let len = nums.len();
    
    if len < 3 {
        false
    } else {
        loop_search(&nums, 0, 2147483647i32, 2147483647i32)
    }
}

fn loop_search(nums: &Vec<i32>, start: usize, first: i32, second: i32) -> (result: bool)
    requires start <= nums.len()
    decreases nums.len() - start
{
    if start >= nums.len() {
        false
    } else {
        let x = nums[start];
        let next_first = if x <= first { x } else { first };
        let next_second = if x > first && x <= second { x } else { second };
        
        if x <= first {
            loop_search(nums, start + 1, next_first, second)
        } else if x <= second {
            loop_search(nums, start + 1, first, next_second)
        } else {
            true  // found triplet
        }
    }
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