// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no-op helper kept for verification */
spec fn dummy_true() -> bool { true }
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
/* code modified by LLM (iteration 5): nested loops with usize quantifiers and safe bounds */
    let n: usize = nums.len();
    if n < 3 { return false; }
    let mut i: usize = 0;
    while i < n - 2
        invariant
            i < n,
            forall|ii: usize, jj: usize, kk: usize|
                ii < jj && jj < kk && kk < n && ii < i ==> !(nums[ii] < nums[jj] && nums[jj] < nums[kk]),
        decreases n - i
    {
        let mut j: usize = i + 1;
        while j < n - 1
            invariant
                i + 1 <= j,
                forall|ii: usize, jj: usize, kk: usize|
                    ii < jj && jj < kk && kk < n &&
                    (ii < i || (ii == i && jj < j)) ==> !(nums[ii] < nums[jj] && nums[jj] < nums[kk]),
            decreases n - j
        {
            let mut k: usize = j + 1;
            while k < n
                invariant
                    j + 1 <= k,
                    forall|ii: usize, jj: usize, kk: usize|
                        ii < jj && jj < kk && kk < n &&
                        (ii < i || (ii == i && jj < j) || (ii == i && jj == j && kk < k)) ==> !(nums[ii] < nums[jj] && nums[jj] < nums[kk]),
                decreases n - k
            {
                if nums[i] < nums[j] && nums[j] < nums[k] {
                    return true;
                }
                k = k + 1;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}