use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
// (no helpers needed)
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
    let n: int = numbers@.len() as int;
    let mut i: int = 0;
    let mut found: bool = false;

    while i < n
        invariant 0 <= i && i <= n;
        invariant found == (exists|p: int, q: int|
            0 <= p && p < q && q < n && p < i && abs(numbers@[p] - numbers@[q]) < threshold);
    {
        let mut j: int = i + 1;
        while j < n && !found
            invariant 0 <= i && i < n;
            invariant i + 1 <= j && j <= n;
            invariant found == (exists|p: int, q: int|
                0 <= p && p < q && q < n && ((p < i) || (p == i && q < j)) && abs(numbers@[p] - numbers@[q]) < threshold);
        {
            if abs(numbers@[i] - numbers@[j]) < threshold {
                found = true;
            }
            j = j + 1;
        }

        if found {
            break;
        }

        i = i + 1;
    }

    found
}
// </vc-code>

fn main() {}
}