// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn increasing_triplet(nums: &Vec<i32>) -> (result: bool)
    ensures
        result ==> exists|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() && 
            nums[i] < nums[j] && nums[j] < nums[k],
        !result ==> forall|i: int, j: int, k: int| 
            0 <= i < j && j < k < nums.len() ==> 
            !(nums[i] < nums[j] && nums[j] < nums[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed bounds checking and invariant correctness */
    let len = nums.len();
    if len < 3 {
        return false;
    }
    
    let mut i = 0;
    while i < len - 2
        invariant
            0 <= i <= len - 2,
            forall|x: int, y: int, z: int| 
                0 <= x < y && y < z < nums.len() && x < i ==> 
                !(nums[x] < nums[y] && nums[y] < nums[z]),
        decreases len - 2 - i
    {
        let mut j = i + 1;
        while j < len - 1
            invariant
                i + 1 <= j <= len - 1,
                0 <= i < len - 2,
                forall|y: int, z: int| 
                    (i as int) < y && y < z < nums.len() && y < j ==> 
                    !(nums[i as int] < nums[y] && nums[y] < nums[z]),
            decreases len - 1 - j
        {
            if i < nums.len() && j < nums.len() && nums[i] < nums[j] {
                let mut k = j + 1;
                while k < len
                    invariant
                        j + 1 <= k <= len,
                        0 <= i < j < len - 1,
                        i < nums.len(),
                        j < nums.len(),
                        nums[i as int] < nums[j as int],
                        forall|z: int| (j as int) < z < nums.len() && z < k ==> !(nums[j as int] < nums[z]),
                    decreases len - k
                {
                    if k < nums.len() && nums[j] < nums[k] {
                        return true;
                    }
                    k += 1;
                }
            }
            j += 1;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}