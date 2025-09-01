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
    let n = numbers.len();
    if n < 2 {
        return false;
    }
    let mut vec = numbers.to_vec();
    vstd::slice::sort(vec.as_mut_slice());
    let mut i = 0;
    while i < vec.len() - 1 {
        invariant forall |k: int| (0 <= k && k < i) ==> #[trigger] abs(vec[k] - vec[k+1]) >= threshold;
        if abs(vec[i] - vec[i+1]) < threshold {
            return true;
        }
        assert(abs(vec[i] - vec[i+1]) >= threshold);
        i = i + 1;
    }
    false
}
// </vc-code>

fn main() {}
}