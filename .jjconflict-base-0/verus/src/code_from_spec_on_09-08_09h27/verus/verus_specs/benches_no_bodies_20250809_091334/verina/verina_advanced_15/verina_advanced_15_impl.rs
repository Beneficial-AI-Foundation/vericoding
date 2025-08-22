use vstd::prelude::*;

verus! {

spec fn increasing_triplet_precond(nums: Seq<i32>) -> bool {
    true
}

fn increasing_triplet(nums: Vec<i32>) -> (result: bool)
    requires increasing_triplet_precond(nums@)
    ensures increasing_triplet_postcond(nums@, result)
{
    let n = nums.len();
    
    if n < 3 {
        return false;
    }
    
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for outer loop */
    while i < n - 2
        invariant 
            0 <= i <= n - 2,
            forall|ii: int, jj: int, kk: int| 
                (0 <= ii < jj && jj < kk && kk < nums@.len() && ii < i) ==> 
                !(nums@[ii] < nums@[jj] && nums@[jj] < nums@[kk])
        decreases n - 2 - i
    {
        let mut j = i + 1;
        /* code modified by LLM (iteration 1): added decreases clause for inner loop */
        while j < n - 1
            invariant 
                i + 1 <= j <= n - 1,
                forall|jj: int, kk: int| 
                    (i < jj && jj < kk && kk < nums@.len() && jj < j) ==> 
                    !(nums@[i as int] < nums@[jj] && nums@[jj] < nums@[kk])
            decreases n - 1 - j
        {
            if nums[i] < nums[j] {
                if loop_search(&nums, j + 1, nums[i], nums[j]) {
                    return true;
                }
            }
            j += 1;
        }
        i += 1;
    }
    
    false
}

fn loop_search(nums: &Vec<i32>, start: usize, first: i32, second: i32) -> (result: bool)
    requires 
        start <= nums.len(),
        first < second
    ensures
        result ==> exists|k: int| start <= k < nums@.len() && second < nums@[k],
        !result ==> forall|k: int| start <= k < nums@.len() ==> second >= nums@[k]
    decreases nums.len() - start
{
    if start >= nums.len() {
        return false;
    }
    
    let mut k = start;
    /* code modified by LLM (iteration 1): added decreases clause for loop in loop_search */
    while k < nums.len()
        invariant 
            start <= k <= nums@.len(),
            forall|kk: int| start <= kk < k ==> second >= nums@[kk]
        decreases nums.len() - k
    {
        if second < nums[k] {
            return true;
        }
        k += 1;
    }
    
    false
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