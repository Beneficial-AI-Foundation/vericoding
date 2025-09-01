use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
use vstd::math::*;
use vstd::prelude::*;

verus! {
    fn i64_abs(a: i64) -> i64 {
        if a < 0 {
            -a
        } else {
            a
        }
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
    let mut temp = Vec::<i64>::with_capacity(numbers.len());
    temp.extend_from_slice(numbers);
    temp.sort();
    proof {
        // Sorting preserves the length
        assert(temp@.len() == numbers@.len());
    }
    let sorted = temp@;

    let len = sorted.len();

    let mut i = 0;

    while i + 1 < len
        invariant
            forall|k: int, l: int| 0 <= k < l < i && i64_abs(sorted@[k] - sorted@[l]) < threshold as int ==> exists|a: int, b: int| 0 <= a < b < numbers@.len() && i64_abs(numbers@[a] - numbers@[b]) < threshold as int,
            i >= 0,
            i <= len,
            exists|k: int, l: int| 0 <= k < l < numbers@.len() && i64_abs(numbers@[k] - numbers@[l]) < threshold as int ==> exists|a: int, b: int| 0 <= a < b < i && i64_abs(sorted@[a] - sorted@[b]) < threshold as int,
    {
        if i64_abs(sorted@[i] - sorted@[i+1]) < threshold as int {
            proof {
                // The invariant ensures that if a close pair exists in the current prefix,
                // it implies existence in the original array due to sorting.
                // Also, i64_abs(sorted@[i] - sorted@[i+1]) < threshold as int is directly the condition.
            }
            return true;
        }
        i += 1;
    }
    return false;
}
// </vc-code>

fn main() {}
}