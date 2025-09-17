// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn unwrap(p: Vec<int>, discont: int, period: int) -> (result: Vec<int>)
    requires 
        discont > 0,
        period > 0,
    ensures
        result.len() == p.len(),
        /* First element is unchanged (if array is non-empty) */
        p.len() > 0 ==> result[0] == p[0],
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