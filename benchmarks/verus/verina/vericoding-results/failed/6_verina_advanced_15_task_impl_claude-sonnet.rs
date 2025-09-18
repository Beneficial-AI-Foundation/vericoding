// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add bound checking helpers with proper int casting */
fn is_valid_triplet(nums: &Vec<i32>, i: usize, j: usize, k: usize) -> bool
    requires
        i < nums.len(),
        j < nums.len(),
        k < nums.len(),
{
    i < j && j < k && nums[i] < nums[j] && nums[j] < nums[k]
}
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
    /* code modified by LLM (iteration 5): fix type mismatch by using int conversion for array indexing */
    let n = nums.len();
    if n < 3 {
        return false;
    }
    
    let mut i = 0;
    while i < n - 2
        invariant
            0 <= i <= n - 2,
            n >= 3,
            forall|x: int, y: int, z: int| 
                0 <= x < y && y < z < n && x < i ==> 
                !(nums@[x] < nums@[y] && nums@[y] < nums@[z]),
        decreases n - 2 - i
    {
        let mut j = i + 1;
        while j < n - 1
            invariant
                i + 1 <= j <= n - 1,
                0 <= i < n - 2,
                n >= 3,
                forall|y: int, z: int| 
                    i < y && y < z < n && y < j ==> 
                    !(nums@[i as int] < nums@[y] && nums@[y] < nums@[z]),
            decreases n - 1 - j
        {
            if i < nums.len() && j < nums.len() && nums@[i as int] < nums@[j as int] {
                let mut k = j + 1;
                while k < n
                    invariant
                        j + 1 <= k <= n,
                        0 <= i < j,
                        j < n - 1,
                        i < nums.len(),
                        j < nums.len(),
                        nums@[i as int] < nums@[j as int],
                        forall|z: int| j < z < k ==> nums@[j as int] >= nums@[z],
                    decreases n - k
                {
                    if k < nums.len() && nums@[j as int] < nums@[k as int] {
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