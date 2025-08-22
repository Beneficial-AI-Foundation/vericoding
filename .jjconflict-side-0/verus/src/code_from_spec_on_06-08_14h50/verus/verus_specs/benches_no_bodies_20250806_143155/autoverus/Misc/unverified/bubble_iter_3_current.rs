use vstd::prelude::*;

verus! {

fn bubble_sort(nums: &mut Vec<i32>) 
    requires nums.len() > 0
    ensures nums.len() == old(nums).len()
{
    let n = nums.len();
    for i in 0..n {
        let mut min_idx = i;
        for j in (i + 1)..n {
            if nums[j] < nums[min_idx] {
                min_idx = j;
            }
        }
        if min_idx != i {
            /* code modified by LLM (iteration 1): fixed syntax from nums.set() to proper swap operation */
            let temp = nums[i];
            nums.set(i, nums[min_idx]);
            nums.set(min_idx, temp);
        }
    }
}

fn main() {}

}