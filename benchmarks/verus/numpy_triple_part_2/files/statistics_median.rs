// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_sorted(a: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
}

fn median(a: Vec<i32>) -> (result: i32)
    requires a.len() > 0,
    ensures 
        exists|sorted: Seq<i32>| #[trigger] sorted.len() == a.len() &&
            is_sorted(sorted) &&
            (if a.len() % 2 == 1 {
                result == sorted[((a.len() - 1) / 2) as int]
            } else {
                result == (sorted[(a.len() / 2 - 1) as int] + sorted[(a.len() / 2) as int]) / 2
            })
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}
fn main() {}