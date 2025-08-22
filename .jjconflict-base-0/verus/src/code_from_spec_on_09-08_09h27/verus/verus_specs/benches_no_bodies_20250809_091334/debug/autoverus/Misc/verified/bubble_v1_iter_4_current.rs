use vstd::prelude::*;

verus! {

spec fn sorted_between(nums: Seq<i32>, start: int, end: int) -> bool {
    forall|i: int, j: int| start <= i < j < end ==> nums[i] <= nums[j]
}

spec fn sorted(nums: Seq<i32>) -> bool {
    sorted_between(nums, 0, nums.len() as int)
}

fn bubble_sort(nums: &mut Vec<i32>)
    requires nums.len() > 0
    ensures sorted(nums@)
{
    let mut i = 0;
    
    while i < nums.len()
        invariant 
            i <= nums.len(),
            sorted_between(nums@, 0, i as int)
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < nums.len()
            invariant
                i <= min_idx < nums.len(),
                i <= j <= nums.len(),
                forall|k: int| i <= k < j ==> nums@[min_idx as int] <= nums@[k]
        {
            if nums[j] < nums[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        if min_idx != i {
            /* code modified by LLM (iteration 1): Fixed syntax for Vec element swapping */
            let temp = nums[i];
            nums.set(i, nums[min_idx]);
            nums.set(min_idx, temp);
        }
        
        i += 1;
    }
}

fn main() {}

}