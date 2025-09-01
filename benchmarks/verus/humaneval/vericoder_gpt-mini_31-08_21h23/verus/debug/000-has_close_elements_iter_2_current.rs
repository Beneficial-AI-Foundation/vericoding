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
    // impl-start
    let n: int = numbers@.len() as int;
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n
        invariant forall|a: int, b: int| 0 <= a && a < b && b < n && a < i ==> abs(numbers@[a] - numbers@[b]) >= threshold
    {
        let mut j: int = i + 1;
        while j < n
            invariant i + 1 <= j && j <= n
            invariant forall|a: int, b: int| 0 <= a && a < b && b < n && a < i ==> abs(numbers@[a] - numbers@[b]) >= threshold
            invariant forall|k: int| i < k && k < j ==> abs(numbers@[i] - numbers@[k]) >= threshold
        {
            if abs(numbers[(i as usize)] - numbers[(j as usize)]) < threshold {
                proof {
                    // connect runtime indexing with specification-level sequence
                    assert(0 <= i);
                    assert(i < j);
                    assert(j < n);
                    assert(numbers[(i as usize)] == numbers@[i]);
                    assert(numbers[(j as usize)] == numbers@[j]);
                    assert(abs(numbers@[i] - numbers@[j]) < threshold);
                }
                return true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    proof {
        // From the outer invariant at i == n, all pairs have distance >= threshold,
        // hence there do not exist close elements.
        assert(forall|a: int, b: int| 0 <= a && a < b && b < n ==> abs(numbers@[a] - numbers@[b]) >= threshold);
        assert(!exists|a: int, b: int| 0 <= a && a < b && b < n && abs(numbers@[a] - numbers@[b]) < threshold);
    }
    false
    // impl-end
}
// </vc-code>

fn main() {}
}