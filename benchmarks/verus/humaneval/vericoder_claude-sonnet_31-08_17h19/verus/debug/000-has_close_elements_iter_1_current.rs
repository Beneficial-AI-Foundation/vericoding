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
    let len = numbers.len();
    for i in 0..len
        invariant
            forall|x: int, y: int| 0 <= x < y < i ==> abs(numbers[x] - numbers[y]) >= threshold,
    {
        for j in (i + 1)..len
            invariant
                forall|x: int, y: int| 0 <= x < y < i ==> abs(numbers[x] - numbers[y]) >= threshold,
                forall|y: int| i < y < j ==> abs(numbers[i as int] - numbers[y]) >= threshold,
        {
            if abs(numbers[i] - numbers[j]) < threshold {
                assert(0 <= i < j < numbers@.len() && abs(numbers[i as int] - numbers[j as int]) < threshold);
                return true;
            }
        }
    }
    false
}
// </vc-code>

fn main() {}
}