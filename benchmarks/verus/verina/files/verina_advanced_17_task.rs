// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i32>) -> (result: Vec<i32>)
    ensures
        /* The result is sorted in non-decreasing order */
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        /* The result is a permutation of the input */
        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
// </vc-code>


}
fn main() {}