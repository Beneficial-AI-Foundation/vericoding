// <vc-preamble>
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed contains method call in exec mode */
fn count_and_select_top_k(nums: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires
        k <= nums@.to_set().len(),
    ensures
        result.len() == k,
        forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        result@.no_duplicates(),
{
    let mut result = Vec::new();
    
    while result.len() < k
        invariant
            result.len() <= k,
            forall|x: i32| result@.contains(x) ==> nums@.contains(x),
            result@.no_duplicates(),
    {
        let mut best_num = 0;
        let mut best_freq = 0;
        let mut found = false;
        
        let mut i = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
        {
            let mut already_included = false;
            let mut j = 0;
            while j < result.len()
                invariant
                    0 <= j <= result.len(),
            {
                if result[j] == nums[i] {
                    already_included = true;
                    break;
                }
                j += 1;
            }
            
            if !already_included {
                let mut freq = 0;
                let mut k = 0;
                while k < nums.len()
                    invariant
                        0 <= k <= nums.len(),
                        freq >= 0,
                {
                    if nums[k] == nums[i] {
                        freq += 1;
                    }
                    k += 1;
                }
                
                if !found || freq > best_freq {
                    best_num = nums[i];
                    best_freq = freq;
                    found = true;
                }
            }
            i += 1;
        }
        
        if found {
            result.push(best_num);
        } else {
            break;
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
fn top_k_frequent(nums: &Vec<i32>, k: usize) -> (result: Vec<i32>)
    requires 
        k <= nums@.to_set().len(),
    ensures
        result.len() == k,
        forall|x: i32| result@.contains(x) ==> nums@.contains(x),
        result@.no_duplicates(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using fixed helper function */
    count_and_select_top_k(nums, k)
}
// </vc-code>

}
fn main() {}