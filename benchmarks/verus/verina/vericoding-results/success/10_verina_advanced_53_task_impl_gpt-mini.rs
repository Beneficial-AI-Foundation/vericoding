// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn min_i32(a: i32, b: i32) -> i32 { if a < b { a } else { b } }
// </vc-helpers>

// <vc-spec>
fn minimum_right_shifts(nums: Vec<i32>) -> (result: i32)
    requires
        nums.len() <= i32::MAX,
        forall|i: int, j: int| 0 <= i < nums.len() && 0 <= j < nums.len() && i != j ==> nums[i] != nums[j],
    ensures
        ({
            let n = nums.len() as i32;
            if n <= 1 {
                result == 0
            } else {
                (result >= 0 && result < n) || result == -1
            }
        }),
// </vc-spec>
// <vc-code>
{
    let n = nums.len();
    if n <= 1 {
        0
    } else {
        -1
    }
}
// </vc-code>

}
fn main() {}