use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    // impl-start
    let n: int = numbers@.len() as int;
    let mut i: int = 0;
    let mut found: bool = false;

    while i < n
        invariant 0 <= i && i <= n
        invariant found == exists|p: int, q: int|
            0 <= p < q < n && p < i && abs(numbers@[p] - numbers@[q]) < threshold
    {
        // inner loop: iterate j from i+1 .. n-1 by initializing j = i and first incrementing
        let mut j: int = i;
        while (j + 1) < n && !found
            invariant 0 <= i && i < n
            invariant i <= j && j < n
            invariant found == exists|p: int, q: int|
                0 <= p < q < n && (p < i || (p == i && q <= j)) && abs(numbers@[p] - numbers@[q]) < threshold
        {
            j = j + 1;
            // check pair (i, j)
            if abs(numbers[j as usize] - numbers[i as usize]) < threshold {
                found = true;
            }
        }

        if found {
            break;
        }

        // at this point, we have checked all pairs with first index == i, so advance i
        i = i + 1;
    }

    found
    // impl-end
}
// </vc-code>

fn main() {}
}