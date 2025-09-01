use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
fn abs_diff(a: i64, b: i64) -> (res: i64)
    ensures res == vstd::math::abs(a - b)
{
    if a >= b {
        (a - b)
    } else {
        (b - a)
    }
}
// </vc-helpers>

// <vc-spec>
fn has_close_elements(numbers: &[i64], threshold: i64) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|i: int, j: int|
            0 <= i < j < numbers@.len() && abs(numbers[i] - numbers[j]) < threshold,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let n = numbers.len();

    for i in 0..n
        invariant
            0 <= i as int <= n as int,
            forall|i_prev: int, j_prev: int| 0 <= i_prev < i as int && i_prev < j_prev < n as int ==> #[trigger] vstd::math::abs(numbers[i_prev] - numbers[j_prev]) >= threshold,
    {
        for j in (i + 1)..n
            invariant
                0 <= i as int < j as int, j as int <= n as int,
                forall|j_prev: int| i as int < j_prev < j as int ==> #[trigger] vstd::math::abs(numbers[i as int] - numbers[j_prev]) >= threshold,
                forall|i_prev: int, j_prev: int| 0 <= i_prev < i as int && i_prev < j_prev < n as int ==> #[trigger] vstd::math::abs(numbers[i_prev] - numbers[j_prev]) >= threshold,
        {
            let diff = abs_diff(numbers[i], numbers[j]);
            if diff < threshold {
                return true;
            }
        }
    }
    proof {
        assert forall|i_val: int, j_val: int|
            0 <= i_val < j_val < n as int implies !(vstd::math::abs(numbers[i_val] - numbers[j_val]) < threshold)
            by {
                // If a pair (i_val, j_val) existed such that abs(numbers[i_val] - numbers[j_val]) < threshold,
                // then based on the loop invariants from the point where the loops complete,
                // this would be a contradiction unless it was caught by the return true statement.
                // The outer loop invariant at the end of the loop ensures that for all i_prev < n, and all j_prev such that i_prev < j_prev < n,
                // abs(numbers[i_prev] - numbers[j_prev]) >= threshold.
                // This directly proves `!exists |i, j| ...`
            }
    }
    false
}
// </vc-code>

fn main() {}
}