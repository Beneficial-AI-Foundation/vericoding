// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn cum_sum(a: Vec<i32>) -> (result: Vec<i32>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        result[0] == a[0],
        forall|i: int| 1 <= i < a.len() ==> result[i] == result[i - 1] + a[i]
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