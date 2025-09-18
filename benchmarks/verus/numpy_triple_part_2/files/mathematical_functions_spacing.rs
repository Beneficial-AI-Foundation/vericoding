// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn spacing(x: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> #[trigger] result[i] > 0
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