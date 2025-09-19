// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn list_merge_properties(a1: Seq<i32>, a2: Seq<i32>, result: Seq<i32>) -> bool {
    result.len() == a1.len() + a2.len()
}

fn merge_sorted_arrays(a1: Vec<i32>, a2: Vec<i32>) -> (result: Vec<i32>)
    ensures list_merge_properties(a1@, a2@, result@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}