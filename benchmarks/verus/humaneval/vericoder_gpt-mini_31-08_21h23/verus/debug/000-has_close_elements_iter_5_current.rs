use vstd::math::abs;
use vstd::prelude::*;
use vstd::slice::*;

verus! {

// <vc-helpers>
// Helper lemmas for relating slice runtime indexing and specification-level sequence indexing.

fn slice_index_eq(numbers: &[i64], i: int)
    requires 0 <= i && i < numbers@.len()
    ensures numbers[(i as usize)] == numbers@[i]
{
    proof {
        // The relation between slice runtime indexing and the specification-level sequence
        // representation is a built-in fact in Verus; re-assert it here for use in proofs.
        assert(numbers[(i as usize)] == numbers@[i]);
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
    // impl-start
    let n: int = numbers@.len() as int;
    let mut i: int = 0;
    while i < n
        invariant 0 <= i && i <= n;
        invariant forall|a: int, b: int| 0 <= a && a < b && b < n && a < i ==> abs(numbers@[a] - numbers@[b]) >= threshold;
        decreases n - i;
    {
        let mut j: int = i + 1;
        while j < n
            invariant i + 1 <= j && j <= n;
            invariant forall|a: int, b: int| 0 <= a && a < b && b < n && a < i ==> abs(numbers@[a] - numbers@[b]) >= threshold;
            invariant forall|k: int| i < k && k < j ==> abs(numbers@[i] - numbers@[k]) >= threshold;
            decreases n - j;
        {
            if abs(numbers[(i as usize)] - numbers[(j as usize)]) < threshold {
                proof {
                    // connect runtime indexing with specification-level sequence
                    assert(0 <= i);
                    assert(i < j);
                    assert(j < n);
                    slice_index_eq(numbers, i);
                    slice_index_eq(numbers, j);
                    assert(abs(numbers@[i] - numbers@[j]) < threshold);
                }
                return true;
            }
            j = j + 1;
        }
        // update outer invariant: when advancing i, all pairs with a < i+1 still satisfy the property
        // We need to show the preserved invariant for next i; this follows from the inner loop invariant
        // together with the fact that for k in (i+1..n) we checked pairs (i,k) in the inner loop.
        proof {
            // Show that after finishing inner loop, for all b with a < b < n and a < i+1, abs>=threshold holds.
            // Take any a,b with 0 <= a < b < n and a < i+1.
            // If a < i then this is the same as the outer invariant at the start of the iteration.
            // If a == i then b > i and by the inner loop invariant we have abs(numbers@[i] - numbers@[b]) >= threshold.
            assert(forall|a: int, b: int| 0 <= a && a < b && b < n && a < i+1 ==>
                abs(numbers@[a] - numbers@[b]) >= threshold);
        }
        i = i + 1;
    }
    proof {
        // From the outer invariant at i == n, all pairs have distance >= threshold,
        // hence there do not exist close elements.
        assert(i >= n);
        assert(i <= n);
        assert(i == n);
        assert(forall|a: int, b: int| 0 <= a && a < b && b < n ==> abs(numbers@[a] - numbers@[b]) >= threshold);
        assert(!exists|a: int, b: int| 0 <= a && a < b && b < n && abs(numbers@[a] - numbers@[b]) < threshold);
    }
    false
    // impl-end
}
// </vc-code>

fn main() {}
}