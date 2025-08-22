use vstd::prelude::*;

verus! {

spec fn is_sorted(nums: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]
}

fn selection_sort(nums: &mut Vec<i32>)
    ensures is_sorted(nums@)
{
    let mut i = 0;
    while i < nums.len()
        invariant 
            i <= nums.len(),
            forall|x: int, y: int| 0 <= x < y < i ==> nums@[x] <= nums@[y],
            forall|x: int, y: int| 0 <= x < i && i <= y < nums@.len() ==> nums@[x] <= nums@[y]
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < nums.len()
            invariant
                i <= min_idx < nums.len(),
                i + 1 <= j <= nums.len(),
                forall|k: int| i <= k < j ==> nums@[min_idx] <= nums@[k]
        {
            if nums[j] < nums[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        if min_idx != i {
            /* code modified by LLM (iteration 1): fixed syntax error by using proper Verus vector element assignment */
            let temp = nums[i];
            nums.set(i, nums[min_idx]);
            nums.set(min_idx, temp);
        }
        
        i += 1;
    }
}

fn main() {}

}