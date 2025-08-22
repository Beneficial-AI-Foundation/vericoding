use vstd::prelude::*;

verus! {

fn bubble_sort(nums: &mut Vec<i32>) 
    /* code modified by LLM (iteration 1): fixed requires clause to use old(nums) for pre-state reference */
    requires old(nums).len() > 0
    ensures nums.len() == old(nums).len()
{
    /* code modified by LLM (iteration 1): implemented proper bubble sort algorithm with correct loop structure and swap operation */
    let n = nums.len();
    for i in 0..n
        invariant nums.len() == old(nums).len()
    {
        for j in 0..(n - 1 - i)
            invariant nums.len() == old(nums).len()
        {
            if nums[j] > nums[j + 1] {
                let temp = nums[j];
                nums.set(j, nums[j + 1]);
                nums.set(j + 1, temp);
            }
        }
    }
}

fn main() {}

}