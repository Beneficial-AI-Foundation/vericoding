use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>

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
    let n = numbers@.len();
    for i in 0..n
        invariant forall |k: int, l: int| 0 <= k < i && k < l < n ==> abs(numbers[k] - numbers[l]) >= threshold
    {
        for j in i+1..n
        {
            invariant forall |k: int, l: int| 0 <= k < i && k < l < n ==> abs(numbers[k] - numbers[l]) >= threshold;
            invariant forall |l: int| i+1 <= l < j ==> abs(numbers[i] - numbers[l]) >= threshold;
            let a = numbers[i];
            let b = numbers[j];
            if abs(a - b) < threshold {
                return true;
            }
        }
    }
    false
}
// </vc-code>

fn main() {}
}