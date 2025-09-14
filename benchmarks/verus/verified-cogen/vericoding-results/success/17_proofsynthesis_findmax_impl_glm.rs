// <vc-preamble>
#[allow(unused_imports)]
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn max_two(a: i32, b: i32) -> (ret: i32)
    ensures
        ret == a || ret == b,
        ret >= a,
        ret >= b,
{
    if a >= b {
        a
    } else {
        b
    }
}
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
/* code modified by LLM (iteration 4): fixed exists quantifier in loop invariant */
{
    let mut current_max = nums[0];
    let mut i: usize = 1;
    while i < nums.len()
        invariant
            i <= nums.len(),
            forall |j: int| 0 <= j < i as int ==> nums@[j] <= current_max,
            exists |j: int| 0 <= j < i as int && nums@[j] == current_max,
        decreases (nums.len() - i) as int,
    {
        let next = nums[i];
        if next > current_max {
            current_max = next;
        }
        i += 1;
    }
    current_max
}
// </vc-code>

}
fn main() {}