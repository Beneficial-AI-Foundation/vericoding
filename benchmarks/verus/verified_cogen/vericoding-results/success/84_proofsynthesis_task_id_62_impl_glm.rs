// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min(a: i32, b: i32) -> (result: i32)
    ensures
        result <= a && result <= b && (result == a || result == b)
{
    if a < b {
        a
    } else {
        b
    }
}
// </vc-helpers>

// <vc-spec>
fn smallest_num(nums: &Vec<i32>) -> (min: i32)

    requires
        nums.len() > 0,

    ensures
        forall|i: int| 0 <= i < nums.len() ==> min <= nums[i],
        exists|i: int| 0 <= i < nums.len() && min == nums[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed while loop clause order and type conversions in invariant */
    let mut min_val = nums[0];
    let mut i: usize = 1;
    
    while i < nums.len()
        invariant
            1 <= i as int <= nums.len() as int,
            forall|j: int| 0 <= j < i as int ==> min_val <= nums@[j],
            exists|j: int| 0 <= j < i as int && min_val == nums@[j],
        decreases nums.len() as int - i as int,
    {
        if nums[i] < min_val {
            min_val = nums[i];
        }
        i += 1;
    }
    
    min_val
}
// </vc-code>

}
fn main() {}