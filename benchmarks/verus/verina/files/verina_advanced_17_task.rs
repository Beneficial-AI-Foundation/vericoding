// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn insertion_sort(l: Vec<i8>) -> (result: Vec<i8>)
    ensures

        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,

        result@.to_multiset() == l@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}