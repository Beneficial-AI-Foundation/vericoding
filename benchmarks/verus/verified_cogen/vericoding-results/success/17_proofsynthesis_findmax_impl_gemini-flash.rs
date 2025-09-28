// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): No helpers needed */
// </vc-helpers>

// <vc-spec>
fn find_max(nums: Vec<i32>) -> (ret:i32)

    requires
        nums.len() > 0,

    ensures
        forall |i: int| 0 <= i < nums@.len() ==> nums@[i] <= ret,
        exists |i: int| 0 <= i < nums@.len() ==> nums@[i] == ret,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed invariant issue by modifying the condition in `exists` clause after `forall` loop and added `assert` statement to prove post-conditions */
{
    let mut max_val: i32 = nums[0];
    let mut i: usize = 1;

    while i < nums.len()
        invariant
            1 <= i,
            i <= nums.len(),
            forall |j: int| 0 <= j < i ==> nums@[j] <= max_val,
            exists |j: int| (0 <= j < i) && (nums@[j] == max_val),
        decreases nums.len() - i
    {
        if nums[i] > max_val {
            max_val = nums[i];
        }
        i = i + 1;
    }

    /* Added assert_ensures to satisfy the postcondition of the function */
    proof {
        assert(forall |k: int| 0 <= k < nums@.len() ==> nums@[k] <= max_val);
        assert(exists |k: int| 0 <= k < nums@.len() ==> nums@[k] == max_val);
    }

    max_val
}
// </vc-code>

}
fn main() {}