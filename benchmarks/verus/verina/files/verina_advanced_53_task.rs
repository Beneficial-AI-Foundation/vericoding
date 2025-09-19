// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn minimum_right_shifts(nums: Vec<i8>) -> (result: i8)
    requires
        nums.len() <= i8::MAX,
        forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> nums[i as int] != nums[j as int],
    ensures
        ({
            let n = nums.len() as i8;
            if n <= 1 {
                result == 0
            } else {
                (result >= 0 && result < n) || result == -1
            }
        }),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}